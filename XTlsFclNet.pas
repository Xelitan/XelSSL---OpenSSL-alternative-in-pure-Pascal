// XTls - fcl-net integration: a TSSLSocketHandler for TInetSocket / TFPHTTPClient.
// Just using the unit registers TXTlsSocketHandler as the default SSL handler.
// It can also be attached to an ALREADY connected socket (STARTTLS): Attach + Connect.
// License: MIT.
unit XTlsFclNet;

{$mode objfpc}{$H+}

interface

uses
  SysUtils, Classes, ssockets, sslsockets, sslbase, XTlsClient, XTlsTrust;

type
  TXTlsSocketHandler = class(TSSLSocketHandler)
  private
    FTls: TXTlsClient;
    FErr: string;
    FHostName: string;
    FCache: TXTlsSessionCache;
    FTrust: TTrustStore;
    function RawSend(const Buf; Len: Integer): Integer;
    function RawRecv(var Buf; Len: Integer): Integer;
  public
    constructor Create; override;
    destructor Destroy; override;
    // the base version raises ("without SSL support"); the client never generates certificates
    function CreateCertGenerator: TX509Certificate; override;
    // attach to an existing, connected socket (e.g. after STARTTLS)
    procedure Attach(AStream: TSocketStream);
    function Connect: Boolean; override;
    function Close: Boolean; override;
    function Shutdown(BiDirectional: Boolean): Boolean; override;
    function Send(const Buffer; Count: Integer): Integer; override;
    function Recv(const Buffer; Count: Integer): Integer; override;
    function BytesAvailable: Integer; override;
    property LastErrorDesc: string read FErr;
    // name for SNI/verification; defaults to TInetSocket.Host
    property HostName: string read FHostName write FHostName;
    property SessionCache: TXTlsSessionCache read FCache write FCache;
    property TrustStore: TTrustStore read FTrust write FTrust;
    property Tls: TXTlsClient read FTls;
  end;

implementation

uses
  {$IFDEF MSWINDOWS}WinSock2{$ELSE}BaseUnix, Sockets{$ENDIF};

{$IFDEF MSWINDOWS}
const
  SEND_FLAGS = 0;
{$ELSE}
const
  {$IFDEF LINUX}SEND_FLAGS = MSG_NOSIGNAL;{$ELSE}SEND_FLAGS = 0;{$ENDIF}
{$ENDIF}

constructor TXTlsSocketHandler.Create;
begin
  inherited Create;
  VerifyPeerCert := True;
end;

destructor TXTlsSocketHandler.Destroy;
begin
  FreeAndNil(FTls);
  inherited Destroy;
end;

function TXTlsSocketHandler.CreateCertGenerator: TX509Certificate;
begin
  Result := nil;
end;

procedure TXTlsSocketHandler.Attach(AStream: TSocketStream);
begin
  SetSocket(AStream);
end;

function TXTlsSocketHandler.RawSend(const Buf; Len: Integer): Integer;
begin
  {$IFDEF MSWINDOWS}
  Result := WinSock2.send(Socket.Handle, Buf, Len, SEND_FLAGS);
  {$ELSE}
  repeat
    Result := fpSend(Socket.Handle, @Buf, Len, SEND_FLAGS);
  until (Result >= 0) or (SocketError <> ESysEINTR);
  {$ENDIF}
end;

function TXTlsSocketHandler.RawRecv(var Buf; Len: Integer): Integer;
begin
  {$IFDEF MSWINDOWS}
  Result := WinSock2.recv(Socket.Handle, Buf, Len, 0);
  {$ELSE}
  repeat
    Result := fpRecv(Socket.Handle, @Buf, Len, 0);
  until (Result >= 0) or (SocketError <> ESysEINTR);
  {$ENDIF}
end;

function TXTlsSocketHandler.Connect: Boolean;
begin
  Result := False;
  FErr := '';
  FreeAndNil(FTls);
  FTls := TXTlsClient.Create(@RawSend, @RawRecv);
  if FHostName <> '' then FTls.Host := FHostName
  else if Socket is TInetSocket then FTls.Host := TInetSocket(Socket).Host;
  FTls.VerifyPeer := VerifyPeerCert;
  FTls.Cache := FCache;
  FTls.Trust := FTrust;
  Result := FTls.Handshake;
  if Result then SetSSLActive(True)
  else
  begin
    FErr := FTls.LastError;
    FLastError := 1;
  end;
end;

function TXTlsSocketHandler.Close: Boolean;
begin
  if (FTls <> nil) and FTls.Connected then FTls.Close;
  SetSSLActive(False);
  Result := True;
end;

function TXTlsSocketHandler.Shutdown(BiDirectional: Boolean): Boolean;
begin
  Result := Close;
end;

function TXTlsSocketHandler.Send(const Buffer; Count: Integer): Integer;
begin
  FLastError := 0;
  if FTls = nil then Exit(-1);
  Result := FTls.Write(Buffer, Count);
  if Result < 0 then begin FErr := FTls.LastError; FLastError := 1; end;
end;

function TXTlsSocketHandler.Recv(const Buffer; Count: Integer): Integer;
begin
  FLastError := 0;
  if FTls = nil then Exit(-1);
  Result := FTls.Read(PByte(@Buffer)^, Count);
  if Result < 0 then begin FErr := FTls.LastError; FLastError := 1; end;
end;

function TXTlsSocketHandler.BytesAvailable: Integer;
begin
  if FTls = nil then Result := 0 else Result := FTls.Pending;
end;

initialization
  TSSLSocketHandler.SetDefaultHandlerClass(TXTlsSocketHandler);
end.
