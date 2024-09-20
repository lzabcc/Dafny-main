/*
 Dafny version of Praxis tokeneer ID station model
 (abstract model)

 See coursework specification (question C) for detail on how to
 extend the model.
 */
 // basic types
 type optional<T> = ts: set<T> | |ts| <= 1   // optional type is modelled as a set with either zero or one element

 type TIME = nat

 const zeroTime := 0

 datatype PRESENCE = present | absent 

 datatype CLEARANCE_CLASS = unmarked | unclassified | restricted | confidential | secret | topsecret

//question2.a
 datatype ADMINOP = overrideLock | archiveLog | updateData | shutdownOp

datatype PRIVILEGE = userOnly | guard | securityOfficer | auditManager

 class Clearance 
 {
    var cClass: CLEARANCE_CLASS
    constructor()
    //question 1.a
    ensures this.cClass == CLEARANCE_CLASS.unmarked 
    {
        cClass := CLEARANCE_CLASS.unmarked;
    }
 }

//question 1.b
ghost function minClearance(c1: Clearance, c2: Clearance): Clearance
  reads c1, c2 
{
    if c1.cClass < c2.cClass then c1 else c2
}

//question 2.b
function availableOps(p: PRIVILEGE): set<ADMINOP>
{
    if p == PRIVILEGE.guard then  {ADMINOP.overrideLock}
    else if p == PRIVILEGE.auditManager then {ADMINOP.archiveLog} 
    else if p == PRIVILEGE.securityOfficer then {ADMINOP.updateData, ADMINOP.shutdownOp}
    //If this function is targeted at users
    else{}
    //If this function is targeted at administrators
    //else  {ADMINOP.overrideLock,ADMINOP.archiveLog,ADMINOP.updateData,ADMINOP.shutdownOp}

}

type USER

type ISSUER = USER

type FINGERPRINT

type FINGERPRINTTEMPLATE

class FingerprintTemplate
{
    var template: FINGERPRINTTEMPLATE
    constructor()
}

// Keys and Certificates
type KEYPART(==)  // can only be instantiated by a type that supports equality

class CertificateId
{
    var issuer: ISSUER
    constructor()
}

trait Certificate
// A certificate is signed, with a certificate id, and has a validity period modelled as a 
// set of times for which it is valid. It can be validated using a key.
{
    var id: CertificateId
    var validityPeriod: set<TIME>
    var isValidatedBy: optional<KEYPART>
}

class IDCert extends Certificate
// An ID certificate also states the subject (user identified by the certificate) and 
// their public key
{
    var subject: USER
    var subjectPubK: KEYPART

    constructor()
}

trait AttCertificate extends Certificate
// All attribute certificates contain the ID of the token and the identification of the 
// ID certificate. 
{
    var baseCertId: CertificateId
    var tokenID: TOKENID
}

class PrivCert extends AttCertificate
// A privilege certificate also contains a role and a clearance
{
    var role: PRIVILEGE
    var clearance: Clearance
    constructor()
}

class AuthCert extends AttCertificate
// Authorisation certificate has the same structure as a privilege 
// certificate
{
    var role: PRIVILEGE
    var clearance: Clearance
    constructor()
}

class IandACert extends AttCertificate
// Identification and Authentication (I and A) certificate also 
// contains a fingerprint template
{
    var template: FingerprintTemplate
    constructor()
}

// Tokens
type TOKENID(==)

class Token
{
    var tokenID: TOKENID
    var idCert: IDCert
    var privCert: PrivCert
    var iandACert: IandACert
    var authCert: optional<AuthCert>

    constructor()

//question3
    predicate ValidToken() 
    reads this,this.idCert, this.privCert, this.iandACert
    {
        privCert.baseCertId == idCert.id &&
        privCert.tokenID == tokenID &&
        iandACert.baseCertId == idCert.id &&
        iandACert.tokenID == tokenID
    }

    predicate TokenwithValidAuth()
    reads this,this.idCert, this.authCert
    {
    exists auth: AuthCert :: auth in this.authCert &&
    auth.baseCertId == this.idCert.id
    && auth.tokenID == this.tokenID
    }
    predicate CurrentToken(now: TIME) 
    reads this, this.idCert, this.privCert, this.iandACert, this.authCert
    {
        ValidToken() &&
        now in this.idCert.validityPeriod &&
        now in this.privCert.validityPeriod &&
        now in this.iandACert.validityPeriod &&
        (forall auth: AuthCert :: auth in this.authCert ==> now in auth.validityPeriod)
    }
}
