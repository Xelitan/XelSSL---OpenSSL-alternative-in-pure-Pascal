// XelSSL - trusted certificate store.
// Windows: system stores ROOT (anchors) and CA (intermediates for path building),
//          excluding certificates in "Disallowed"; plus a fallback verification via the
//          system chain engine (CertGetCertificateChain + SSL policy) - it fetches
//          missing roots through Windows automatic root update.
// Unix/macOS/BSD: SSL_CERT_FILE / SSL_CERT_DIR or well-known CA bundle paths.
// CryptoAPI declarations and the path list follow TlsLib4Pascal (MIT). License: MIT.
unit XelSslTrust;

{$mode objfpc}{$H+}

interface

uses
  SysUtils, Classes, StrUtils, SyncObjs, XelSslHash, XelSslX509;

type
  TTrustStore = class
  private
    FAnchors, FPool: TCertArray;
    FLock: SyncObjs.TCriticalSection;
  public
    constructor Create;
    destructor Destroy; override;
    procedure AddDer(const Der: TBytes; AsAnchor: Boolean = True);
    function AddPem(const Pem: RawByteString; AsAnchor: Boolean = True): Integer;   // number added
    function AddFile(const FileName: string; AsAnchor: Boolean = True): Integer;
    procedure LoadSystem;
    function Verify(const Chain: array of TBytes; const Host: string; out Err: string): TVerifyResult;
    property Anchors: TCertArray read FAnchors;
    property Pool: TCertArray read FPool;
  end;

// Shared system store (loaded on first use).
function SystemTrust: TTrustStore;

// Extracts DER certificates from PEM text.
function PemCertificates(const Pem: RawByteString): TBytesArray;

implementation

{$IFDEF MSWINDOWS}
uses Windows;

const
  CRYPT32 = 'crypt32.dll';
  MY_ENCODING_TYPE = $00010001;
  CERT_STORE_PROV_MEMORY = PAnsiChar(2);
  CERT_STORE_ADD_ALWAYS = 4;
  USAGE_MATCH_TYPE_AND = 0;
  AUTHTYPE_SERVER = 2;
  CERT_CHAIN_POLICY_SSL = PAnsiChar(4);
  SZOID_SERVER_AUTH: PAnsiChar = '1.3.6.1.5.5.7.3.1';

type
  HCERTSTORE = Pointer;
  PCERT_CONTEXT = ^CERT_CONTEXT;
  CERT_CONTEXT = record
    dwCertEncodingType: DWORD;
    pbCertEncoded: PByte;
    cbCertEncoded: DWORD;
    pCertInfo: Pointer;
    hCertStore: HCERTSTORE;
  end;
  CERT_ENHKEY_USAGE = record
    cUsageIdentifier: DWORD;
    rgpszUsageIdentifier: Pointer;
  end;
  CERT_USAGE_MATCH = record
    dwType: DWORD;
    Usage: CERT_ENHKEY_USAGE;
  end;
  CERT_CHAIN_PARA = record
    cbSize: DWORD;
    RequestedUsage: CERT_USAGE_MATCH;
  end;
  CERT_CHAIN_POLICY_PARA = record
    cbSize: DWORD;
    dwFlags: DWORD;
    pvExtraPolicyPara: Pointer;
  end;
  CERT_CHAIN_POLICY_STATUS = record
    cbSize: DWORD;
    dwError: DWORD;
    lChainIndex: LongInt;
    lElementIndex: LongInt;
    pvExtraPolicyStatus: Pointer;
  end;
  SSL_EXTRA_CERT_CHAIN_POLICY_PARA = record
    cbSize: DWORD;
    dwAuthType: DWORD;
    fdwChecks: DWORD;
    pwszServerName: PWideChar;
  end;

function CertOpenSystemStoreW(hProv: Pointer; szSubsystemProtocol: PWideChar): HCERTSTORE; stdcall; external CRYPT32;
function CertEnumCertificatesInStore(hCertStore: HCERTSTORE; pPrev: PCERT_CONTEXT): PCERT_CONTEXT; stdcall; external CRYPT32;
function CertCloseStore(hCertStore: HCERTSTORE; dwFlags: DWORD): BOOL; stdcall; external CRYPT32;
function CertOpenStore(lpszStoreProvider: PAnsiChar; dwEncodingType: DWORD; hCryptProv: Pointer;
  dwFlags: DWORD; pvPara: Pointer): HCERTSTORE; stdcall; external CRYPT32;
function CertCreateCertificateContext(dwCertEncodingType: DWORD; pbCertEncoded: PByte;
  cbCertEncoded: DWORD): PCERT_CONTEXT; stdcall; external CRYPT32;
function CertFreeCertificateContext(pCertContext: PCERT_CONTEXT): BOOL; stdcall; external CRYPT32;
function CertAddEncodedCertificateToStore(hCertStore: HCERTSTORE; dwCertEncodingType: DWORD;
  pbCertEncoded: PByte; cbCertEncoded: DWORD; dwAddDisposition: DWORD; ppCertContext: Pointer): BOOL; stdcall; external CRYPT32;
function CertGetCertificateChain(hChainEngine: Pointer; pCertContext: PCERT_CONTEXT; pTime: Pointer;
  hAdditionalStore: HCERTSTORE; const pChainPara: CERT_CHAIN_PARA; dwFlags: DWORD; pvReserved: Pointer;
  out ppChainContext: Pointer): BOOL; stdcall; external CRYPT32;
procedure CertFreeCertificateChain(pChainContext: Pointer); stdcall; external CRYPT32;
function CertVerifyCertificateChainPolicy(pszPolicyOID: PAnsiChar; pChainContext: Pointer;
  const pPolicyPara: CERT_CHAIN_POLICY_PARA; var pPolicyStatus: CERT_CHAIN_POLICY_STATUS): BOOL; stdcall; external CRYPT32;

procedure CollectStore(const Name: UnicodeString; var Into: TBytesArray);
var st: HCERTSTORE; ctx: PCERT_CONTEXT; der: TBytes;
begin
  st := CertOpenSystemStoreW(nil, PWideChar(Name));
  if st = nil then Exit;
  try
    ctx := CertEnumCertificatesInStore(st, nil);
    while ctx <> nil do
    begin
      if (ctx^.cbCertEncoded > 0) and (ctx^.pbCertEncoded <> nil) then
      begin
        SetLength(der, ctx^.cbCertEncoded);
        Move(ctx^.pbCertEncoded^, der[0], ctx^.cbCertEncoded);
        SetLength(Into, Length(Into) + 1);
        Into[High(Into)] := der;
      end;
      ctx := CertEnumCertificatesInStore(st, ctx);
    end;
  finally
    CertCloseStore(st, 0);
  end;
end;

// Verification with the Windows engine: chain + SSL policy (EKU serverAuth, host name).
function OsVerify(const Chain: array of TBytes; const Host: string): Boolean;
var
  leaf: PCERT_CONTEXT; mem: HCERTSTORE; chainCtx: Pointer; i: Integer;
  usage: array[0..0] of PAnsiChar; cp: CERT_CHAIN_PARA; pp: CERT_CHAIN_POLICY_PARA;
  ssl: SSL_EXTRA_CERT_CHAIN_POLICY_PARA; status: CERT_CHAIN_POLICY_STATUS; wHost: UnicodeString;
begin
  Result := False;
  if (Length(Chain) = 0) or (Length(Chain[0]) = 0) then Exit;
  leaf := CertCreateCertificateContext(MY_ENCODING_TYPE, @Chain[0][0], Length(Chain[0]));
  if leaf = nil then Exit;
  mem := CertOpenStore(CERT_STORE_PROV_MEMORY, MY_ENCODING_TYPE, nil, 0, nil);
  chainCtx := nil;
  try
    if mem <> nil then
      for i := 1 to High(Chain) do
        if Length(Chain[i]) > 0 then
          CertAddEncodedCertificateToStore(mem, MY_ENCODING_TYPE, @Chain[i][0], Length(Chain[i]),
            CERT_STORE_ADD_ALWAYS, nil);
    usage[0] := SZOID_SERVER_AUTH;
    FillChar(cp, SizeOf(cp), 0);
    cp.cbSize := SizeOf(cp);
    cp.RequestedUsage.dwType := USAGE_MATCH_TYPE_AND;
    cp.RequestedUsage.Usage.cUsageIdentifier := 1;
    cp.RequestedUsage.Usage.rgpszUsageIdentifier := @usage[0];
    if not CertGetCertificateChain(nil, leaf, nil, mem, cp, 0, nil, chainCtx) then Exit;
    FillChar(ssl, SizeOf(ssl), 0);
    ssl.cbSize := SizeOf(ssl);
    ssl.dwAuthType := AUTHTYPE_SERVER;
    wHost := UnicodeString(Host);
    if Host <> '' then ssl.pwszServerName := PWideChar(wHost);
    FillChar(pp, SizeOf(pp), 0);
    pp.cbSize := SizeOf(pp);
    pp.pvExtraPolicyPara := @ssl;
    FillChar(status, SizeOf(status), 0);
    status.cbSize := SizeOf(status);
    if not CertVerifyCertificateChainPolicy(CERT_CHAIN_POLICY_SSL, chainCtx, pp, status) then Exit;
    Result := status.dwError = 0;
  finally
    if chainCtx <> nil then CertFreeCertificateChain(chainCtx);
    if mem <> nil then CertCloseStore(mem, 0);
    CertFreeCertificateContext(leaf);
  end;
end;
{$ENDIF}

// ---- PEM ----

function PemCertificates(const Pem: RawByteString): TBytesArray;
const
  BeginTag = '-----BEGIN CERTIFICATE-----';
  EndTag = '-----END CERTIFICATE-----';
  B64 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';
var
  p, e, i, v, bits, n, idx: Integer; acc: UInt32; der: TBytes; c: AnsiChar;
begin
  Result := nil;
  p := Pos(BeginTag, Pem);
  while p > 0 do
  begin
    e := PosEx(EndTag, Pem, p);
    if e = 0 then Break;
    SetLength(der, (e - p) * 3 div 4 + 3);
    n := 0; acc := 0; bits := 0;
    for i := p + Length(BeginTag) to e - 1 do
    begin
      c := Pem[i];
      idx := Pos(c, B64);
      if idx = 0 then Continue;                   // skip whitespace and '='
      v := idx - 1;
      acc := (acc shl 6) or UInt32(v);
      Inc(bits, 6);
      if bits >= 8 then
      begin
        Dec(bits, 8);
        der[n] := Byte(acc shr bits);
        Inc(n);
      end;
    end;
    SetLength(der, n);
    SetLength(Result, Length(Result) + 1);
    Result[High(Result)] := der;
    p := PosEx(BeginTag, Pem, e);
  end;
end;

// ---- TTrustStore ----

constructor TTrustStore.Create;
begin
  inherited Create;
  FLock := SyncObjs.TCriticalSection.Create;
end;

destructor TTrustStore.Destroy;
begin
  FLock.Free;
  inherited Destroy;
end;

procedure TTrustStore.AddDer(const Der: TBytes; AsAnchor: Boolean);
var c: TCert;
begin
  if not ParseCert(Der, c) then Exit;
  FLock.Enter;
  try
    if AsAnchor then
    begin
      SetLength(FAnchors, Length(FAnchors) + 1);
      FAnchors[High(FAnchors)] := c;
    end
    else
    begin
      SetLength(FPool, Length(FPool) + 1);
      FPool[High(FPool)] := c;
    end;
  finally
    FLock.Leave;
  end;
end;

function TTrustStore.AddPem(const Pem: RawByteString; AsAnchor: Boolean): Integer;
var certs: TBytesArray; i: Integer;
begin
  certs := PemCertificates(Pem);
  for i := 0 to High(certs) do AddDer(certs[i], AsAnchor);
  Result := Length(certs);
end;

function TTrustStore.AddFile(const FileName: string; AsAnchor: Boolean): Integer;
var fs: TFileStream; s: RawByteString; b: TBytes;
begin
  Result := 0;
  if not FileExists(FileName) then Exit;
  fs := TFileStream.Create(FileName, fmOpenRead or fmShareDenyNone);
  try
    SetLength(s, fs.Size);
    if fs.Size > 0 then fs.ReadBuffer(s[1], fs.Size);
  finally
    fs.Free;
  end;
  if Pos('-----BEGIN', s) > 0 then Result := AddPem(s, AsAnchor)
  else if Length(s) > 0 then
  begin
    SetLength(b, Length(s));
    Move(s[1], b[0], Length(s));
    AddDer(b, AsAnchor);
    Result := 1;
  end;
end;

procedure TTrustStore.LoadSystem;
{$IFDEF MSWINDOWS}
var roots, cas, bad: TBytesArray; i, j: Integer; skip: Boolean;
begin
  roots := nil; cas := nil; bad := nil;
  CollectStore('Disallowed', bad);
  CollectStore('ROOT', roots);
  CollectStore('CA', cas);
  for i := 0 to High(roots) do
  begin
    skip := False;
    for j := 0 to High(bad) do if SameBytesCT(roots[i], bad[j]) then skip := True;
    if not skip then AddDer(roots[i], True);
  end;
  for i := 0 to High(cas) do
  begin
    skip := False;
    for j := 0 to High(bad) do if SameBytesCT(cas[i], bad[j]) then skip := True;
    if not skip then AddDer(cas[i], False);       // intermediates - only for path building
  end;
end;
{$ELSE}
const
  Files: array[0..5] of string = (
    '/etc/ssl/certs/ca-certificates.crt',      // Debian, Ubuntu, Alpine, Gentoo
    '/etc/pki/tls/certs/ca-bundle.crt',         // Fedora, RHEL, CentOS
    '/etc/ssl/ca-bundle.pem',                   // openSUSE
    '/etc/ssl/cert.pem',                        // macOS, OpenBSD, Alpine
    '/usr/local/etc/ssl/cert.pem',              // FreeBSD
    '/usr/local/share/certs/ca-root-nss.crt');  // FreeBSD (ports)
  Dirs: array[0..2] of string = ('/etc/ssl/certs', '/etc/openssl/certs', '/etc/certs/CA');
var f, d: string; i: Integer; sr: TSearchRec;
begin
  f := GetEnvironmentVariable('SSL_CERT_FILE');
  if (f <> '') and (AddFile(f) > 0) then Exit;
  d := GetEnvironmentVariable('SSL_CERT_DIR');
  for i := 0 to High(Files) do
    if AddFile(Files[i]) > 0 then Exit;
  if d = '' then
    for i := 0 to High(Dirs) do
      if DirectoryExists(Dirs[i]) then begin d := Dirs[i]; Break; end;
  if (d <> '') and (FindFirst(IncludeTrailingPathDelimiter(d) + '*', faAnyFile, sr) = 0) then
  begin
    repeat
      if (sr.Attr and faDirectory) = 0 then AddFile(IncludeTrailingPathDelimiter(d) + sr.Name);
    until FindNext(sr) <> 0;
    FindClose(sr);
  end;
end;
{$ENDIF}

function TTrustStore.Verify(const Chain: array of TBytes; const Host: string; out Err: string): TVerifyResult;
var a, p: TCertArray;
begin
  FLock.Enter;
  try a := FAnchors; p := FPool; finally FLock.Leave; end;
  Result := VerifyChain(Chain, Host, a, p, NowUtc, Err);
  {$IFDEF MSWINDOWS}
  // no known root: Windows may not have it in the store yet (it fetches roots
  // while building chains) - ask the system engine, which also checks the host name
  if (Result = vrUnknownCA) and (Self = SystemTrust) and OsVerify(Chain, Host) then
  begin
    Result := vrOk; Err := '';
  end;
  {$ENDIF}
end;

var
  GSystem: TTrustStore = nil;
  GSysLock: SyncObjs.TCriticalSection;

function SystemTrust: TTrustStore;
begin
  if GSystem = nil then
  begin
    GSysLock.Enter;
    try
      if GSystem = nil then
      begin
        Result := TTrustStore.Create;
        Result.LoadSystem;
        GSystem := Result;
      end;
    finally
      GSysLock.Leave;
    end;
  end;
  Result := GSystem;
end;

initialization
  GSysLock := SyncObjs.TCriticalSection.Create;
finalization
  FreeAndNil(GSystem);
  FreeAndNil(GSysLock);
end.
