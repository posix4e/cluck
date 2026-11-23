import Kernel.Net.Flat

/-! A small web server for the trial TCP (`Kernel/Net/Flat.lean`), to try it with: `GET /` gets a page,
`GET /big` a large one, anything else is not found. It is the application that TCP wants, a function and
a list of ready answers, and no more of HTTP than that takes.

A request is over at its first empty line. The connection then stays open for another, as HTTP/1.1 has
it, unless the request said `Connection: close`, when the answer says so too and the stream ends after
it. What is kept between the runs of bytes of one request is a number: how much of the empty line has
been seen, whether closing was asked for, which page.

What it does not do: the request's first line, and the words `Connection: close`, must each come whole
in one run of bytes (one segment); a request with a body is not understood; HTTP/1.0, which closes
unless told otherwise, is answered as 1.1; and a second request sent before the first is answered is not
taken until it is sent again (see `Flat`). -/

namespace Kernel.Net.FlatHttp

open Kernel.Net.Flat

def page (status : String) (body : ByteArray) (closing : Bool) : ByteArray :=
  s!"HTTP/1.1 {status}\r\nContent-Type: text/plain\r\nContent-Length: {body.size}\r\n{if closing then "Connection: close\r\n" else ""}\r\n".toUTF8 ++ body

/-- The answers: `/`, `/big` and not found as sent when the stream then ends, and the same three as sent
when the connection stays open. -/
def pages (big : ByteArray) : Array ByteArray :=
  let bodies := #[("200 OK", "a TCP written in Lean\n".toUTF8), ("200 OK", big), ("404 Not Found", "nothing here\n".toUTF8)]
  (bodies.map fun (status, body) => page status body true) ++ (bodies.map fun (status, body) => page status body false)

/-- Which page a request's first line asks for: 1 for `/`, 2 for `/big`, 3 for anything else. -/
@[inline] def pathOf (rx : @& ByteArray) (at_ length : USize) : UInt32 :=
  if length ≥ 6 && rd32 rx at_ == 0x47455420 && rd16 rx (at_ + 4) == 0x2f20 then 1
  else if length ≥ 9 && rd32 rx at_ == 0x47455420 && rd32 rx (at_ + 4) == 0x2f626967 && rd8 rx (at_ + 8) == 0x20 then 2
  else 3

/-- Whether the words `Connection: close` are among the bytes from `i` to `stop`. Eight bytes are looked at
together for the letter the words begin with, and only where it is are the words compared. -/
partial def asksClose (rx : @& ByteArray) (i stop : USize) : Bool :=
  if i + 17 > stop then false else
  let w := rd64 rx i ^^^ 0x4343434343434343
  if (w - 0x0101010101010101) &&& ~~~w &&& 0x8080808080808080 == 0 then asksClose rx (i + 8) stop
  else if rd64 rx i == 0x436f6e6e65637469 && rd64 rx (i + 8) == 0x6f6e3a20636c6f73 && rd8 rx (i + 16) == 0x65 then true
  else asksClose rx (i + 1) stop

/-- How much of the empty line that ends a request (`\r\n\r\n`) the bytes from `i` to `stop` end with,
when those before ended with `blank` of it; 4 is all of it, and the looking stops there. -/
partial def blankIn (rx : @& ByteArray) (i stop : USize) (blank : UInt32) : UInt32 :=
  if i ≥ stop || blank == 4 then blank else
  let byte := rd8 rx i
  blankIn rx (i + 1) stop (
    if byte == 13 then (if blank == 2 then 3 else 1)
    else if byte == 10 then (if blank == 1 then 2 else if blank == 3 then 4 else 0)
    else 0)

/-- The application: `number` is 0 when a request begins; then its three lowest bits are how much of the
empty line has been seen, the fourth whether closing was asked for, the two above which page. A request
that comes whole in one run and ends it, as nearly all do, is known by its last four bytes. -/
def respond (rx : ByteArray) (at_ length : USize) (number : UInt32) : UInt64 :=
  let which : UInt32 := if number &&& 0x30 != 0 then (number >>> 4) &&& 3 else pathOf rx at_ length
  let asked := number &&& 8 != 0 || asksClose rx at_ (at_ + length)
  let blank :=
    if number &&& 7 == 0 && length ≥ 4 && rd32 rx (at_ + length - 4) == 0x0d0a0d0a then 4
    else blankIn rx at_ (at_ + length) (number &&& 7)
  if blank == 4 then (if asked then send (which - 1) 0 else sendOn (which + 2) 0)
  else more (blank ||| (if asked then (8 : UInt32) else 0) ||| (which <<< 4))

end Kernel.Net.FlatHttp
