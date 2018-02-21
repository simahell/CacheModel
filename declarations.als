open util/ordering[Time]

/***********************

Network Component

***********************/
abstract sig NetworkEndpoint{}
abstract sig HTTPConformist extends NetworkEndpoint{cache : lone Cache}
sig HTTPServer extends HTTPConformist{}
abstract sig HTTPClient extends HTTPConformist{
	owner:WebPrincipal // owner of the HTTPClient process
}
sig Browser extends HTTPClient {
	trustedCA : set certificateAuthority
}

/*sig InternetExplorer extends Browser{}
sig InternetExplorer7 extends InternetExplorer{}
sig InternetExplorer8 extends InternetExplorer{}
sig Firefox extends Browser{}
sig Firefox3 extends Firefox {}
sig Safari extends Browser{}*/

abstract sig HTTPIntermediary extends HTTPConformist{}
sig HTTPProxy extends HTTPIntermediary{}
sig HTTPGateway extends HTTPIntermediary{}

fact MoveOfIntermediary{
	all tr:HTTPTransaction |{
		//通常のユーザ + WEBATTACKERが所有する中継者のふるまい
		//応答を行う場合、その応答を得る別のトランザクションがリクエストとレスポンスの間に存在する
		(tr.request.to in HTTPIntermediary) and (tr.request.to in WebPrincipal.servers) and (one tr.response) implies{
			some tr':HTTPTransaction |{
				tr != tr'

				//tr.req -> tr'.req -> tr'.res -> tr.res
				tr'.request.current in tr.request.current.*next
				tr.response.current in tr'.response.current.*next

				tr'.request.from = tr.request.to
				tr'.request.uri = tr.request.uri
				tr.response.body = tr'.response.body
				tr.response.statusCode = tr'.response.statusCode
			}
		}
	}
}

fact ReqAndResMaker{
	no req:HTTPRequest | req.from in HTTPServer
	no req:HTTPRequest | req.to in HTTPClient
	no res:HTTPResponse | res.from in HTTPClient
	no res:HTTPResponse | res.to in HTTPServer
}


/***********************

Event

***********************/
abstract sig Event {current : one Time}

abstract sig NetworkEvent extends Event {
	from: NetworkEndpoint,
	to: NetworkEndpoint
}{
	from != to
}

abstract sig HTTPEvent extends NetworkEvent {
	headers: set HTTPHeader,
	host : Origin,
	uri: one Uri,
	body: set Token
}

sig HTTPRequest extends HTTPEvent {
	// host + path == url
	method: Method,
	path : Path,
	queryString : set attributeNameValuePair,  // URL query string parameters
}
sig HTTPResponse extends HTTPEvent {
	statusCode: one Status
}
sig CacheReuse extends NetworkEvent{target: one HTTPResponse}{}

//firstがsecondよりも前に発生しているか確認
pred happensBefore[first:Event,second:Event]{
	second.current in first.current.next.*next
}

//HTTPResponseの発生条件
fact happenResponse{
	all res:HTTPResponse | one req:HTTPRequest |{
		//レスポンスに対する条件
		happensBefore[req, res]
		res.uri = req.uri
		res.from = req.to
		res.to = req.from

		//HTTPTransactionに登録
		one t:HTTPTransaction | t.request = req and t.response = res

		//所属するTransactionはただ一つ
		one tr:HTTPTransaction | res = tr.response
	}
}

//CacheReuseの発生条件
fact happenCacheReuse{
	all reuse:CacheReuse | one str:StateTransaction |
		{
			str.re_res = reuse
			reuse.to = str.request.from
			reuse.from in str.request.(from + to)

			some pre, post:CacheState |
				(post in str.afterState and LastState[pre, post, str]) implies
					{
						reuse.target in pre.dif.store
						reuse.from.cache = pre.eq.cache
					}

			reuse.target.uri = str.request.uri
		}
}

//ある再利用を行うトランザクションでレスポンス時点で検証済みか判定
pred checkVerification[str:StateTransaction]{
	one str.re_res	//再利用で応答している

	//検証を行っているトランザクションが成立している
	some str':StateTransaction |	//tr': 検証を行うトランザクション
	{
		str' != str
		one str'.response	//検証のレスポンスが存在する
		str'.cause = str	//検証の通信の発生元

		str'.request.current in str.request.current.*next	//tr.request => tr'.request
		str.re_res.current in str'.response.current.*next	//tr'.response => tr.reuse

		str'.request.from = str.re_res.from
		str'.request.to = str.re_res.target.from
		str'.request.uri = str.request.uri

		some h:HTTPHeader |{
			h in ETagHeader + LastModifiedHeader
			h in str.re_res.target.headers
		}

		//格納レスポンスのヘッダに適した条件付きリクエストのヘッダを生成
		(some h:ETagHeader | h in str.re_res.target.headers) implies	//格納レスポンスがETagHeaderを持っていた場合、IfNoneMatchHeaderを付けて送信
			(some h:IfNoneMatchHeader | h in str'.request.headers)
		(some h:LastModifiedHeader | h in str.re_res.target.headers) implies	//格納レスポンスがLastModifiedHeaderを持っていた場合、IfModifiedSinceHeaderを付けて送信
			(some h:IfModifiedSinceHeader | h in str'.request.headers)
	}
}

//条件付きリクエストのトランザクション
fact ConditionalRequestTransaction{
	all tr:HTTPTransaction |
		(some h:HTTPHeader | h in IfNoneMatchHeader + IfModifiedSinceHeader and h in tr.request.headers) implies
		{
			//検証後はそのURIに対する格納レスポンスはただ一つ
			one res:HTTPResponse |
			{
				res.uri = tr.response.uri
				one cs:CacheState |
				{
					res in cs.dif.store
					cs.eq.cache = tr.request.from.cache
					cs in tr.afterState
				}
			}

			//レスポンスの状態コード
			tr.response.statusCode in c200 + c304

			//再利用不可(c200)である場合、検証結果のレスポンスが格納される（既に格納済みであったレスポンスはすべて削除される）
			tr.response.statusCode = c200 implies
			{
				all cs:CacheState |
					(cs in tr.afterState and cs.eq.cache = tr.response.to.cache) implies
						tr.response in cs.dif.store
			}

			//再利用可(c304)である場合、検証結果のレスポンスは格納されない（既に格納済みであったレスポンスのうち一つが残る）
			tr.response.statusCode = c304 implies
			{
				all cs:CacheState |
					(cs in tr.afterState and cs.eq.cache = tr.response.to.cache) implies
						tr.response !in cs.dif.store
			}
		}
}


/***********************

Headers

************************/
abstract sig HTTPHeader {}
abstract sig HTTPResponseHeader extends HTTPHeader{}
abstract sig HTTPRequestHeader extends HTTPHeader{}
abstract sig HTTPGeneralHeader extends HTTPHeader{}
abstract sig HTTPEntityHeader extends HTTPHeader{}

sig IfModifiedSinceHeader extends HTTPRequestHeader{}
sig IfNoneMatchHeader extends HTTPRequestHeader{}
sig ETagHeader extends HTTPResponseHeader{}
sig LastModifiedHeader extends HTTPResponseHeader{}
sig AgeHeader extends HTTPResponseHeader{}
sig CacheControlHeader extends HTTPGeneralHeader{options : set CacheOption}
sig DateHeader extends HTTPGeneralHeader{}
sig ExpiresHeader extends HTTPEntityHeader{}

abstract sig CacheOption{}
abstract sig RequestCacheOption extends CacheOption{}
abstract sig ResponseCacheOption extends CacheOption{}
sig Maxage,NoCache,NoStore,NoTransform extends CacheOption{}
sig MaxStale,MinFresh,OnlyIfCached extends RequestCacheOption{}
sig MustRevalidate,Public,Private,ProxyRevalidate,SMaxage extends ResponseCacheOption{}

//どのリクエスト・レスポンスにも属さないヘッダは存在しない
//各ヘッダは適切なリクエスト・レスポンスに属する
//どのCacheControlヘッダにも属さないCacheOptiionは存在しない
fact noOrphanedHeaders {
	all h:HTTPRequestHeader|some req:HTTPRequest|h in req.headers
	all h:HTTPResponseHeader|some resp:HTTPResponse|h in resp.headers
	all h:HTTPGeneralHeader|some e:HTTPEvent | h in e.headers
	all h:HTTPEntityHeader|some e:HTTPEvent | h in e.headers
	all c:CacheOption | c in CacheControlHeader.options
	all c:RequestCacheOption | c in HTTPRequest.headers.options
	all c:ResponseCacheOption | c in HTTPResponse.headers.options
}

//CacheControlHeaderのオプションに関する制限
fact CCHeaderOption{
	//for "no-cache"
	all str:StateTransaction |
		(some op:NoCache | op in (str.request.headers.options + str.re_res.target.headers.options)) implies
			some str.re_res implies
				checkVerification[str]

	//for "no-store"
	all res:HTTPResponse |
		(some op:NoStore | op in res.headers.options) implies
			all cs:CacheState | res !in cs.dif.store

	/*
	//for only-if-cached
	all req:HTTPRequest | (some op:OnlyIfCached | op in req.headers.options) implies {
		some reuse:CacheReuse | {
			happensBefore[req, reuse]
			reuse.target.uri = req.uri
			reuse.to = req.from
		}
	}
	*/

	//for "private"
	all res:HTTPResponse |
		(some op:Private | op in res.headers.options) implies
			all cs:CacheState | res in cs.dif.store implies cs.eq.cache in PrivateCache
}

/****************************

Cache

****************************/
abstract sig Cache{}
sig PrivateCache extends Cache{}
sig PublicCache extends Cache{}

//どの端末にも属さないキャッシュは存在しない
fact noOrphanedCaches {
	all c:Cache |
		one e:NetworkEndpoint | c = e.cache
}

//PrivateCacheとPrivateCacheの場所の制限
fact PublicAndPrivate{
	all pri:PrivateCache | pri in HTTPClient.cache
	all pub:PublicCache | (pub in HTTPServer.cache) or (pub in HTTPIntermediary.cache)
}

sig CacheState extends State{}{
	eq in CacheEqItem
	dif in CacheDifItem

	eq.cache in PrivateCache implies
        all res:HTTPResponse | res in dif.store implies
                {
                    (one op:Maxage | op in res.headers.options) or
                    (one d:DateHeader, e:ExpiresHeader | d in res.headers and e in res.headers)
                }

    eq.cache in PublicCache implies
        all res:HTTPResponse | res in dif.store implies
                {
                    (one op:Maxage | op in res.headers.options) or
                    (one op:SMaxage | op in res.headers.options) or
                    (one d:DateHeader, e:ExpiresHeader | d in res.headers and e in res.headers)
                }

    all res:HTTPResponse | res in dif.store implies
        one h:AgeHeader | h in res.headers
}
sig CacheEqItem extends EqItem{cache: one Cache}
sig CacheDifItem extends DifItem{store: set HTTPResponse}

//同じ内容のCacheEqItem, CacheDifItemは統合される
fact noMultipleItems{
	no disj i,i':CacheEqItem | i.cache = i'.cache
	no disj i,i':CacheDifItem | i.store = i'.store
}

//キャッシュを持つ端末を含むTransaction => StateTransactionである
//すべてのStateTransactionは、リクエストのfrom/toに含まれるキャッシュの状態をbeforeStateに持つ
//すべてのStateTransactionは、レスポンスor再利用を持つ場合、beforeStateで状態を持っているキャッシュの状態をafterStateに持つ
fact CacheInTransaction{
	all tr:HTTPTransaction |
		(some tr.request.(from + to).cache implies tr in StateTransaction)

	all str:StateTransaction |{
		str.beforeState.eq.cache = str.request.(from + to).cache
		some str.(request + re_res) implies str.afterState.eq.cache = str.beforeState.eq.cache
	}
}

fact flowCacheState{
	//初期状態のstoreをnullにする
	all cs:CacheState |
		InitialState[cs] implies
			no cs.dif.store

	//直前のキャッシュの状態を継承する（responseの場合はそれを格納可能）
	all pre, post:CacheState, str:StateTransaction |
		LastState[pre, post, str] implies {
			post in str.beforeState implies post.dif.store in pre.dif.store
			post in str.afterState implies post.dif.store in (pre.dif.store + str.response)
		}
}


/************************

DNS

************************/
sig DNS{
	parent : DNS + DNSRoot,
	resolvesTo : set NetworkEndpoint
}{
// A DNS Label resolvesTo something
	some resolvesTo
}

one sig DNSRoot {}

//全てのDNSについて、自身からたどれるparentの集合に自身は含まれない
fact dnsIsAcyclic {
	 all x: DNS | x !in x.^parent
//	 all x:dns-dnsRoot | some x.parent
}

// s is  a subdomain of d
//sのparentをたどるとdが存在する⇔sがdのサブドメインである
pred isSubdomainOf[s: DNS, d: DNS]{
	//e.g. .stanford.edu is a subdomain of .edu
	d in s.*parent
}

//DNSから対象のPrincipalを取得
fun getPrincipalFromDNS[dns : DNS]:Principal{
	dnslabels.dns
}

//Originから対象のPrincipalを取得
fun getPrincipalFromOrigin[o: Origin]:Principal{
	getPrincipalFromDNS[o.dnslabel]
}

//異なるプリンシパルは同じDNS、同じサーバを持たない
fact DNSIsDisjointAmongstPrincipals {
	all disj p1,p2 : Principal | (no (p1.dnslabels & p2.dnslabels)) and ( no (p1.servers & p2.servers))
//The servers disjointness is a problem for virtual hosts. We will replace it with disjoint amongst attackers and trusted people or something like that
}

// turn this on for intermediate checks
// run show {} for 6


/***********************

Token

************************/
sig Time {}

fact Traces{
	all t:Time | one e:Event | t = e.current
}

abstract sig Token {}
//秘匿情報 作成者、期限を持つ
abstract sig Secret extends Token {
	madeBy : Principal,
	expiration : lone Time,
}

sig Uri{}

//使用されないURIは存在しない
fact noOrphanedUri{
	all u:Uri | some e:HTTPEvent | u = e.uri
}

sig URL {path:Path, host:Origin}

abstract sig Method {}
one sig GET extends Method {}
one sig PUT  extends Method {}
one sig POST extends Method {}
one sig DELETE extends Method {}
one sig OPTIONS extends Method {}

fun safeMethods[]:set Method {
	GET+OPTIONS
}

//レスポンスの状態コード
abstract sig Status  {}
abstract sig RedirectionStatus extends Status {}

lone sig c200,c401 extends Status{}
lone sig c301,c302,c303,c304,c305,c306,c307 extends RedirectionStatus {}


/***********************

User

***********************/
abstract sig Principal {
// without the -HTTPClient the HTTPS check fails
	servers : set NetworkEndpoint,
	dnslabels : set DNS,
}

//Passive Principals match their http / network parts
abstract sig PassivePrincipal extends Principal{}{
	servers in HTTPConformist
}

abstract sig WebPrincipal extends PassivePrincipal {
	httpClients : set HTTPClient
}{
	all c:HTTPClient | c in httpClients implies c.owner = this
}

sig Alice extends WebPrincipal {}

sig ACTIVEATTACKER extends Principal{}
sig PASSIVEATTACKER extends PassivePrincipal{}
sig WEBATTACKER extends WebPrincipal{}

abstract sig NormalPrincipal extends WebPrincipal{} { 	dnslabels.resolvesTo in servers}
lone sig GOOD extends NormalPrincipal{}
lone sig SECURE extends NormalPrincipal{}
lone sig ORIGINAWARE extends NormalPrincipal{}

fact noOrphanedPoint{
	all e:NetworkEndpoint |
		one p:Principal |
			e in p.(servers + httpClients)
}

fact NonActiveFollowHTTPRules {
// Old rule was :
//	all t:HTTPTransaction | t.resp.from in HTTPServer implies t.req.host.server = t.resp.from
// We rewrite to say HTTPAdherents cant spoof from part ... here we don't say anything about principal
	all httpresponse:HTTPResponse | httpresponse.from in HTTPConformist implies httpresponse.from in httpresponse.host.dnslabel.resolvesTo
}

fact SecureIsHTTPSOnly {
// Add to this the fact that transaction schema is consistent
	all httpevent:HTTPEvent | httpevent.from in SECURE.servers implies httpevent.host.schema = HTTPS
//	STS Requirement : all sc : ScriptContext | some (getPrincipalFromOrigin[sc.owner] & SECURE ) implies sc.transactions.req.host.schema=HTTPS
}

fact CSRFProtection {
	all aResp:HTTPResponse | aResp.from in ORIGINAWARE.servers and aResp.statusCode=c200 implies {
		(response.aResp).request.method in safeMethods or (
		let theoriginchain = ((response.aResp).request.headers & OriginHeader).theorigin |
			some theoriginchain and theoriginchain.dnslabel in ORIGINAWARE.dnslabels
		)
	}
}

fact NormalPrincipalsHaveNonTrivialDNSValues {
// Normal Principals don't mess around with trivial DNS values
   DNSRoot !in NormalPrincipal.dnslabels.parent
}

fact WebPrincipalsObeyTheHostHeader {
	all aResp:HTTPResponse |
		let p = servers.(aResp.from) |
			p in WebPrincipal implies {
				//the host header a NormalPrincipal Sets is always with the DNSLabels it owns
				aResp.host.dnslabel in p.dnslabels
				// it also makes sure that the from server is the same one that the dnslabel resolvesTo
				aResp.from in aResp.host.dnslabel.resolvesTo

				//additionally it responds to some request and keep semantics similar to the way Browsers keep them
				some t:HTTPTransaction | t.response = aResp and t.request.host.dnslabel = t.response.host.dnslabel and t.request.host.schema = t.response.host.schema
			}
}

fact NormalPrincipalsDontMakeRequests {
	no aReq:HTTPRequest | aReq.from in NormalPrincipal.servers
}


/***********************************

Client Definitions

************************************/
// Each user is associated with a set of network locations
// from where they use their credentials
pred isAuthorizedAccess[user:WebPrincipal, loc:NetworkEndpoint]{
	loc in user.httpClients
}

/*
fun smartClient[]:set Browser {
	Firefox3 + InternetExplorer8
}
*/

sig WWWAuthnHeader extends HTTPResponseHeader{}{
  all resp:HTTPResponse| (some (WWWAuthnHeader & resp.headers)) => resp.statusCode=c401
}

// each user has at most one password
sig UserPassword extends UserToken { }

// sig AliceUserPassword extends UserPassword {} {id = Alice and madeBy in Alice }

pred somePasswordExists {
  some UserPassword //|p.madeBy in Alice
}

//run somePasswordExists for 8

pred basicModelIsConsistent {
  some ScriptContext
  some t1:HTTPTransaction |{
    some (t1.request.from & Browser ) and
    some (t1.response)
  }
}

// Browsers run a scriptContext
sig ScriptContext {
	owner : Origin,
	location : Browser,
	transactions: set HTTPTransaction
}{
// Browsers are honest, they set the from correctly
	transactions.request.from = location
}

sig attributeNameValuePair { name: Token, value: Token}

sig LocationHeader extends HTTPResponseHeader {
	targetOrigin : Origin,
	targetPath : Path,
	params : set attributeNameValuePair  // URL request parameters
}
//sig location extends HTTPResponseHeader {targetOrigin : Origin, targetPath : Path}
// The name location above easily conflicts with other attributes and variables with the same name.
// We should follow the convention of starting type names with a capital letter.
// Address this in later clean-up.

abstract sig RequestAPI{} // extends Event


/************************

HTTPTransaction

************************/
sig HTTPTransaction {
	request : one HTTPRequest,
	response : lone HTTPResponse,
	re_res : lone CacheReuse,
	cert : lone Certificate,
	cause : lone HTTPTransaction + RequestAPI
}{
	some response implies {
		//response can come from anyone but HTTP needs to say it is from correct person and hosts are the same, so schema is same
		response.host = request.host
		happensBefore[request,response]
	}

	some re_res implies {
		happensBefore[request, re_res]
	}

	request.host.schema = HTTPS implies some cert and some response
	some cert implies request.host.schema = HTTPS
}

fact limitHTTPTransaction{
	all req:HTTPRequest | lone t:HTTPTransaction | t.request = req
	all res:HTTPResponse | lone t:HTTPTransaction | t.response = res
	all reuse:CacheReuse | lone t:HTTPTransaction | t.re_res = reuse
	no t:HTTPTransaction |
		some t.response and some t.re_res
}

fact CauseHappensBeforeConsequence  {
	all t1: HTTPTransaction | some (t1.cause) implies {
       (some t0:HTTPTransaction | (t0 in t1.cause and happensBefore[t0.response, t1.request]))
		or (some r0:RequestAPI | (r0 in t1.cause ))
       // or (some r0:RequestAPI | (r0 in t1.cause and happensBefore[r0, t1.req]))
    }
}

fun getTrans[e:HTTPEvent]:HTTPTransaction{
	(request+response).e
}

fun getScriptContext[t:HTTPTransaction]:ScriptContext {
		transactions.t
}

fun getContextOf[req:HTTPRequest]:Origin {
	(transactions.(request.req)).owner
}

pred isCrossOriginRequest[request:HTTPRequest]{
		getContextOf[request].schema != request.host.schema or
		getContextOf[request].dnslabel != request.host.dnslabel
}


/************************************
* CSRF
*
************************************/
// RFC talks about having Origin Chain and not a single Origin
// We handle Origin chain by having multiple Origin Headers
sig OriginHeader extends HTTPRequestHeader {theorigin: Origin}


fun getFinalResponse[req:HTTPRequest]:HTTPResponse{
		{res : HTTPResponse | not ( res.statusCode in RedirectionStatus) and res in ((request.req).*(~cause)).response}
}

pred isFinalResponseOf[req:HTTPRequest, res : HTTPResponse] {
		not ( res.statusCode in RedirectionStatus)
		res in ((request.req).*(~cause)).response
}

//enum Port{P80,P8080}
enum Schema{HTTP,HTTPS}
sig Path{}
sig INDEX,HOME,SENSITIVE, PUBLIC, LOGIN,LOGOUT,REDIRECT extends Path{}
sig PATH_TO_COMPROMISE extends SENSITIVE {}

sig Origin {
//	port: Port,
	schema: Schema,
	dnslabel : DNS,
}

abstract sig certificateAuthority{}
one sig BADCA,GOODCA extends certificateAuthority{}

sig Certificate {
	ca : certificateAuthority,
	cn : DNS,
	ne : NetworkEndpoint
}{

	//GoodCAVerifiesNonTrivialDNSValues
	ca in GOODCA and cn.parent != DNSRoot implies
			some p:Principal | {
				cn in p.dnslabels
				ne in p.servers
				ne in cn.resolvesTo
			}
}


/****************************

Cookie Stuff

****************************/
// Currently the String type is taken but not yet implemented in Alloy
// We will replace String1 with String when the latter is fully available in Alloy
sig String1 {}

sig UserToken extends Secret {
        id : WebPrincipal
}

sig Cookie extends Secret {
	name : Token,
	value : Token,
	domain : DNS,
	path : Path,
}{}

sig SecureCookie extends Cookie {}

sig CookieHeader extends HTTPRequestHeader{ thecookie : Cookie }
sig SetCookieHeader extends HTTPResponseHeader{	thecookie : Cookie }

fact SecureCookiesOnlySentOverHTTPS{
		all e:HTTPEvent,c:SecureCookie | {
				e.from in Browser + NormalPrincipal.servers
				httpPacketHasCookie[c,e]
		} implies e.host.schema=HTTPS

}

fact CookiesAreSameOriginAndSomeOneToldThemToTheClient{
	all areq:HTTPRequest |{
			areq.from in Browser
			some ( areq.headers & CookieHeader)
	} implies  all acookie :(areq.headers & CookieHeader).thecookie | some aresp: location.(areq.from).transactions.response | {
				//don't do same origin check as http cookies can go over https
				aresp.host.dnslabel = areq.host.dnslabel
				acookie in (aresp.headers & SetCookieHeader).thecookie
				happensBefore[aresp,areq]
	}
}

pred httpPacketHasCookie[c:Cookie,httpevent:HTTPRequest+HTTPResponse]{
				(httpevent in HTTPRequest and  c in (httpevent.headers & CookieHeader).thecookie ) or
				(httpevent in HTTPResponse and c in (httpevent.headers & SetCookieHeader).thecookie)
}

pred hasKnowledgeViaUnencryptedHTTPEvent[c: Cookie, ne : NetworkEndpoint, usageEvent: Event]{
		ne !in WebPrincipal.servers + Browser
		some httpevent : HTTPEvent | {
			happensBefore[httpevent,usageEvent]
			httpevent.host.schema = HTTP
			httpPacketHasCookie[c,httpevent]
		}
}

pred hasKnowledgeViaDirectHTTP[c:Cookie,ne:NetworkEndpoint,usageEvent:Event]{
		some t: HTTPTransaction | {
		happensBefore[t.request,usageEvent]
		httpPacketHasCookie[c,t.request]
		t.response.from = ne
	} or {
		happensBefore[t.response,usageEvent]
		httpPacketHasCookie[c,t.response]
		some ((transactions.t).location & ne)
		}
}

pred hasKnowledgeCookie[c:Cookie,ne:NetworkEndpoint,usageEvent:Event]{
	ne in c.madeBy.servers or hasKnowledgeViaUnencryptedHTTPEvent[c,ne,usageEvent] or hasKnowledgeViaDirectHTTP[c,ne,usageEvent]
}

fact BeforeUsingCookieYouNeedToKnowAboutIt{
	all e:HTTPRequest + HTTPResponse |
// Use httpPacketHasCookie
			all c:(e.(HTTPRequest <: headers) & CookieHeader).thecookie + (e.(HTTPResponse <: headers) & SetCookieHeader).thecookie |
					hasKnowledgeCookie[c,e.from,e]
}

fact NormalPrincipalsOnlyUseCookiesTheyMade{
	all e:HTTPResponse |
		all c:(e.headers & SetCookieHeader).thecookie | {
			e.from in NormalPrincipal.servers implies c.madeBy = e.from[servers]
		}
}

fact NormalPrincipalsDontReuseCookies{
	all p:NormalPrincipal | no disj e1,e2:HTTPResponse | {
			(e1.from + e2.from) in p.servers
			some ( 	(e1.headers & SetCookieHeader).thecookie & (e2.headers & SetCookieHeader).thecookie )
	}
}

/*
run show2 {
	some (SetCookieHeader).thecookie
} for 6
*/


/***********************

HTTP Facts

************************/
fact scriptContextsAreSane {
	all disj sc,sc':ScriptContext | no (sc.transactions & sc'.transactions)
	all t:HTTPTransaction | t.request.from in Browser implies t in ScriptContext.transactions
}

fact HTTPTransactionsAreSane {
	all disj t,t':HTTPTransaction | no (t.response & t'.response ) and no (t.request & t'.request)
}


/***********************

State

************************/
abstract sig State{
	flow: set State,
	eq: one EqItem,
	dif: one DifItem,
	current: set Time
}
abstract sig EqItem{}
abstract sig DifItem{}

sig StateTransaction extends HTTPTransaction{
	beforeState: set State,
	afterState: set State
}

//同じeqをもつ => 同じbefore/afterStateに存在しない
//同じeq,difを持つStateは存在しない
fact noMultipleState{
	all str:StateTransaction |
		all disj s,s':CacheState |
			s.eq = s'.eq implies
				{
					s in str.beforeState implies s' !in str.beforeState
					s in str.afterState implies s' !in str.afterState
				}

	no disj s,s':State |{
		s.eq = s'.eq
		s.dif = s'.dif
	}
}

//すべてのStateは、どこかのbefore/afterStateに属する
//すべてのStateTransactionは、before/afterStateにStateを持つ
//使用されていないEq/DifItemは存在しない
fact noOrphanedStates{
	all s:State | s in StateTransaction.(beforeState + afterState)
	all str:StateTransaction | some str.(beforeState + afterState)
	all i:EqItem | i in State.eq
	all i:DifItem | i in State.dif
}

//flowに関する条件
fact catchStateFlow{
	all pre,post:State, str:StateTransaction |
		LastState[pre, post, str] implies
			post in pre.flow
	all s,s':State |
		s' in s.flow implies
			(some str:StateTransaction | LastState[s, s', str])
}

//StateがbeforeStateに属する <=> Stateがリクエストの時間を持つ
//StateがafterStateに属する <=> Stateがレスポンスの時間を持つ
fact StateCurrentTime{
	all s:State |
		all str:StateTransaction |
			{
				s in str.beforeState iff str.request.current in s.current
				s in str.afterState iff str.(response + re_res).current in s.current
			}

	all t:Time |
		t in State.current implies t in StateTransaction.(request + response + re_res).current
}

//preがpostの直前の状態か確認
pred LastState[pre:State, post:State, str:StateTransaction]{
	pre.eq = post.eq
	post in str.(beforeState + afterState)

	some t,t':Time |
		{
			//t:pre, t':post
			//pre->post
			t in pre.current
			t' in str.(request + response + re_res).current
			t' in str.request.current implies post in str.beforeState
			t' in str.(response + re_res).current implies post in str.afterState
			t' in t.next.*next

			all s:State, t'':Time |
				(s.eq = pre.eq and t'' in s.current) implies	//t'':s
						(t in t''.*next) or (t'' in t'.*next)	//s => pre (or) post => cs
		}
}

//sが初期状態か確認
pred InitialState[s:State]{
	all s':State |
		s.eq = s'.eq implies
			s'.current in s.current.*next	//s => s'
}
