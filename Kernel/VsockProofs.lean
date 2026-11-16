import Kernel.Vsock

/-! # What is proved about the vsock protocol

The protocol's state is a table of connections, and every byte the parent sends reaches it. Two things are
proved about it here, for every packet and every call, whatever they contain.

The table stays bounded: no packet, and no sequence of packets and calls, makes it hold more connections than
the endpoint allows (`receive_bounded` and the others, `bounded_always`). A parent cannot make the machine
remember without limit.

A write never takes more than the peer has said it has room for, nor more than it was given
(`write_within_room`).

Not proved: that the packets a write emits carry exactly the bytes it says it took, and anything about the
counters once they wrap. Those are covered by the scenarios and the fuzzer in `vsock-test`.

Nothing that runs imports this file; `Gate.lean` does. -/

namespace Kernel.Vsock

/-- The table holds no more connections than the endpoint allows. -/
def Endpoint.Bounded (e : Endpoint) : Prop := e.conns.size ≤ e.maxConns

theorem put_conns (e : Endpoint) (i : Nat) (c : Conn) :
    (e.put i c).conns.size = e.conns.size ∧ (e.put i c).maxConns = e.maxConns := by
  simp [Endpoint.put]

theorem remove_conns (e : Endpoint) (key : Key) :
    (e.remove key).conns.size ≤ e.conns.size ∧ (e.remove key).maxConns = e.maxConns := by
  simp only [Endpoint.remove, and_true]
  exact Array.size_filter_le

theorem put_bounded {e : Endpoint} (h : e.Bounded) (i : Nat) (c : Conn) : (e.put i c).Bounded := by
  have := put_conns e i c
  simp only [Endpoint.Bounded] at *
  omega

theorem remove_bounded {e : Endpoint} (h : e.Bounded) (key : Key) : (e.remove key).Bounded := by
  have := remove_conns e key
  simp only [Endpoint.Bounded] at *
  omega

theorem abort_bounded {e : Endpoint} (h : e.Bounded) (c : Conn) : (e.abort c).1.Bounded := by
  simp only [Endpoint.abort]
  exact remove_bounded h _

theorem onConnected_bounded {e : Endpoint} (h : e.Bounded) (i : Nat) (c : Conn) (p : Packet) :
    (e.onConnected i c p).1.Bounded := by
  unfold Endpoint.onConnected
  repeat (first | exact put_bounded h _ _ | exact remove_bounded h _ | exact abort_bounded h _ | split | dsimp only)

theorem onConnecting_bounded {e : Endpoint} (h : e.Bounded) (i : Nat) (c : Conn) (p : Packet) :
    (e.onConnecting i c p).1.Bounded := by
  unfold Endpoint.onConnecting
  repeat (first | exact put_bounded h _ _ | exact remove_bounded h _ | exact abort_bounded h _ | split | dsimp only)

/-- A request to connect adds a connection only where there is room for one. -/
theorem onUnknown_bounded {e : Endpoint} (h : e.Bounded) (key : Key) (p : Packet) :
    (e.onUnknown key p).1.Bounded := by
  unfold Endpoint.onUnknown
  split
  · exact h
  · dsimp only
    split
    · split
      · exact h
      · simp only [Endpoint.Bounded, Array.size_push] at *
        omega
    · split
      · simp only [Endpoint.Bounded] at *
        exact Nat.le_trans Array.size_filter_le h
      · simp only [Endpoint.Bounded, Array.size_push] at *
        omega

/-- **One packet from the device, whatever is in it, leaves the table within its bound.** -/
theorem receive_bounded {e : Endpoint} (h : e.Bounded) (raw : ByteArray) : (e.receive raw).1.Bounded := by
  unfold Endpoint.receive
  repeat (first
    | exact h | exact onUnknown_bounded h _ _ | exact onConnected_bounded h _ _ _
    | exact onConnecting_bounded h _ _ _ | exact abort_bounded h _ | split | dsimp only)

theorem write_bounded {e : Endpoint} (h : e.Bounded) (key : Key) (bytes : ByteArray) :
    (e.write key bytes).1.Bounded := by
  unfold Endpoint.write
  repeat (first | exact h | exact put_bounded h _ _ | split | dsimp only)

theorem askForRoom_bounded {e : Endpoint} (h : e.Bounded) (key : Key) : (e.askForRoom key).1.Bounded := by
  unfold Endpoint.askForRoom
  repeat (first | exact h | exact put_bounded h _ _ | split | dsimp only)

theorem close_bounded {e : Endpoint} (h : e.Bounded) (key : Key) : (e.close key).1.Bounded := by
  unfold Endpoint.close
  repeat (first | exact h | exact put_bounded h _ _ | split | dsimp only)

theorem connect_bounded {e : Endpoint} (h : e.Bounded) (key : Key) : (e.connect key).1.Bounded := by
  unfold Endpoint.connect
  split
  · exact h
  · simp only [Endpoint.Bounded, Array.size_push, Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at *
    omega

/-- Anything that can happen to an endpoint: a packet from the device, or one of the calls the machine makes. -/
inductive Step where
  | receive (raw : ByteArray)
  | write (key : Key) (bytes : ByteArray)
  | askForRoom (key : Key)
  | connect (key : Key)
  | close (key : Key)

def Endpoint.step (e : Endpoint) : Step → Endpoint
  | .receive raw => (e.receive raw).1
  | .write key bytes => (e.write key bytes).1
  | .askForRoom key => (e.askForRoom key).1
  | .connect key => (e.connect key).1
  | .close key => (e.close key).1

/-- **The table is bounded for good.** After any sequence of packets and calls, an endpoint that started
within its bound is within it. -/
theorem bounded_always {e : Endpoint} (h : e.Bounded) (steps : List Step) :
    (steps.foldl Endpoint.step e).Bounded := by
  induction steps generalizing e with
  | nil => exact h
  | cons step rest ih =>
    apply ih
    cases step with
    | receive raw => exact receive_bounded h raw
    | write key bytes => exact write_bounded h key bytes
    | askForRoom key => exact askForRoom_bounded h key
    | connect key => exact connect_bounded h key
    | close key => exact close_bounded h key

/-- An endpoint with no connections is within its bound. -/
theorem empty_bounded (e : Endpoint) (h : e.conns = #[]) : e.Bounded := by
  simp [Endpoint.Bounded, h]

/-- **A write takes no more than the peer has room for, and no more than it was given.** -/
theorem write_within_room (e : Endpoint) (key : Key) (bytes : ByteArray) :
    (e.write key bytes).2.2 ≤ bytes.size ∧
      ∀ i c, e.find? key = some (i, c) → (e.write key bytes).2.2 ≤ c.peerFree := by
  unfold Endpoint.write
  constructor
  · repeat (first | exact Nat.zero_le _ | exact Nat.min_le_left _ _ | split | dsimp only)
  · intro i c found
    rw [found]
    dsimp only
    split
    · exact Nat.zero_le _
    · exact Nat.min_le_right _ _

end Kernel.Vsock
