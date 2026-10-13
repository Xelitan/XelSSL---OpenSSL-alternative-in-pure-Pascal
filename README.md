# XelSSL — a TLS 1.2 / 1.3 client in pure Pascal

About 5,000 lines, no DLLs and no OpenSSL. Works on every platform supported by
Free Pascal. It also replaces TlsLib4Pascal + CryptoLib4Pascal (~435,000 lines):
Makes EXEs about 5 MB smaller than EXEs using TlsLib4Pascal.

## Limitations

- client only (no server mode, no client certificates — an empty one is sent when requested);
- no revocation checking (CRL/OCSP), like most non-browser clients;
- no CBC suites and no RSA key exchange in TLS 1.2 (ECDHE + AEAD only);
- no 0-RTT, compression, Ed25519/Ed448 or Brainpool curves in certificates;
- tested on Windows; the Unix code paths (`/dev/urandom`, CA bundle files, sockets) have not been built or run yet.

## Usage

With fcl-net it is enough to add `XTlsFclNet` to `uses` — it registers itself as the
default SSL handler, so `TFPHTTPClient` handles `https://` URLs. To upgrade an
already connected socket (STARTTLS), use `TXTlsSocketHandler.Attach` + `Connect`.
`TXTlsClient` can also be used directly with any transport (two callbacks: send
and receive raw bytes).

## License

MIT — see [LICENSE](LICENSE), which also credits the authors of the code this library builds on.
