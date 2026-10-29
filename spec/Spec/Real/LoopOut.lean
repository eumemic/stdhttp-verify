import Spec.Real.LoopWrite

/-!
# Pending output does not change what the write loop does

`TO O m` is `m` with `O` in front of its pending output. Every write to the output buffer appends
(`ChunkedBuffer.push`, `append`), and nothing reads it, so the write loop on `TO O m` is the write
loop on `m` with `O` in front (`pw_TO`). The loop needs this where one run sends an interim
`100 Continue` an iteration before the other.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Strict HttpSpec.RealMachine HttpSpec.RealSegment HttpSpec.RealAbsorb

namespace HttpSpec.RealLoop

/-! ## Appending to the output buffer -/

/-- `f` writes after what is in the buffer. -/
def PH (f : ChunkedBuffer → ChunkedBuffer) : Prop := ∀ O b : ChunkedBuffer, f (O.append b) = O.append (f b)

theorem ph_push (x : _root_.ByteArray) : PH (fun b => b.push x) := by
  intro O b
  simp only [ChunkedBuffer.push, ChunkedBuffer.append, Array.append_push, Nat.add_assoc]

theorem ph_write (x : _root_.ByteArray) : PH (fun b => b.write x) := ph_push x

theorem ph_writeString (s : String) : PH (fun b => b.writeString s) := ph_push _

theorem ph_writeChar (c : Char) : PH (fun b => b.writeChar c) := ph_push _

theorem ph_append (c : ChunkedBuffer) : PH (fun b => b.append c) := by
  intro O b
  simp only [ChunkedBuffer.append, Array.append_assoc, Nat.add_assoc]

theorem ph_id : PH id := fun _ _ => rfl

theorem ph_comp {f g : ChunkedBuffer → ChunkedBuffer} (hf : PH f) (hg : PH g) : PH (fun b => g (f b)) := by
  intro O b; dsimp only; rw [hf, hg]

theorem ph_foldl {α : Type} (g : ChunkedBuffer → α → ChunkedBuffer) (hg : ∀ a, PH (fun b => g b a)) :
    ∀ (l : List α), PH (fun b => l.foldl g b)
  | [] => fun _ _ => rfl
  | a :: as => by
    intro O b
    simp only [List.foldl_cons]
    rw [show g (O.append b) a = O.append (g b a) from hg a O b]
    exact ph_foldl g hg as O (g b a)

theorem ph_afoldl {α : Type} (g : ChunkedBuffer → α → ChunkedBuffer) (hg : ∀ a, PH (fun b => g b a))
    (l : Array α) : PH (fun b => l.foldl g b) := by
  intro O b
  dsimp only
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact ph_foldl g hg l.toList O b

theorem ph_version (v : Version) : PH (fun b => Encode.encode (v := .v11) b v) := ph_push _

theorem ph_headers (h : Headers) : PH (fun b => Encode.encode (v := .v11) b h) := by
  intro O b
  show h.map.toArray.foldl _ (O.append b) = O.append (h.map.toArray.foldl _ b)
  exact ph_afoldl _ (fun _ => ph_push _) _ O b

theorem ph_responseHead (r : Response.Head) : PH (fun b => Encode.encode (v := .v11) b r) :=
  ph_comp (ph_comp (ph_comp (ph_comp (ph_comp (ph_comp (ph_comp (ph_version r.version) (ph_writeChar ' '))
    (ph_writeString _)) (ph_writeChar ' ')) (ph_writeString _)) (ph_writeString _)) (ph_headers r.headers))
    (ph_writeString _)

theorem ph_chunk (c : Chunk) : PH (fun b => Encode.encode (v := .v11) b c) := by
  intro O b
  exact ph_append _ O b

theorem ph_msgHead (h : Protocol.H1.Message.Head Direction.receiving.swap) :
    PH (fun b => Encode.encode (v := .v11) b h) := ph_responseHead h

theorem ph_msgHead' (O b : ChunkedBuffer) (h : Protocol.H1.Message.Head Direction.receiving.swap) :
    Encode.encode (v := .v11) (O.append b) h = O.append (Encode.encode (v := .v11) b h) := ph_msgHead h O b

theorem ph_resp' (O b : ChunkedBuffer) (h : Response.Head) :
    Encode.encode (v := .v11) (O.append b) h = O.append (Encode.encode (v := .v11) b h) := ph_responseHead h O b

/-! ## The write loop with output in front -/

/-- `m` with `O` in front of its pending output. -/
def TO (O : ChunkedBuffer) (m : Machine .receiving) : Machine .receiving :=
  { m with writer := { m.writer with outputData := O.append m.writer.outputData } }

section
variable (O : ChunkedBuffer) (m : Machine .receiving)

theorem TO_setWriterState (s : Writer.State) : TO O (m.setWriterState s) = (TO O m).setWriterState s := rfl
theorem TO_addEvent (e : Event .receiving) : TO O (m.addEvent e) = (TO O m).addEvent e := rfl
theorem TO_setError (e : Error) : TO O (m.setError e) = (TO O m).setError e := rfl
theorem TO_disableKeepAlive : TO O m.disableKeepAlive = (TO O m).disableKeepAlive := rfl
theorem TO_closeWriter : TO O m.closeWriter = (TO O m).closeWriter := rfl
theorem TO_closeReader : TO O m.closeReader = (TO O m).closeReader := rfl
theorem TO_setReaderState (s : Reader.State .receiving) : TO O (m.setReaderState s) = (TO O m).setReaderState s := rfl
theorem TO_closeOnBadMessage : TO O m.closeOnBadMessage = (TO O m).closeOnBadMessage := rfl
theorem TO_userClosedBody : TO O m.userClosedBody = (TO O m).userClosedBody := rfl
theorem TO_setKnownSize (sz : Body.Length) : TO O (m.setKnownSize sz) = (TO O m).setKnownSize sz := rfl

theorem TO_isReaderAwaitingContinue : (TO O m).isReaderAwaitingContinue = m.isReaderAwaitingContinue := by
  unfold Machine.isReaderAwaitingContinue
  cases h : m.reader.state <;> simp [TO, h]

theorem TO_reset : TO O m.resetForNextMessage = (TO O m).resetForNextMessage := by
  unfold Machine.resetForNextMessage
  by_cases hk : m.keepAlive = true
  · have hk' : (TO O m).keepAlive = true := hk
    rw [if_pos hk, if_pos hk']; rfl
  · have hk' : ¬ (TO O m).keepAlive = true := hk
    rw [if_neg hk, if_neg hk']; rfl

theorem TO_writeHead (h : Protocol.H1.Message.Head Direction.receiving.swap) :
    TO O (m.writeHead h) = (TO O m).writeHead h := by
  obtain ⟨⟨st, inp, mh, mc, bbr, hbr, nmi⟩, w, c, ev, er, ins, ka, ff, pbs⟩ := m
  obtain ⟨meth, ver, uri, hdrs⟩ := (mh : Request.Head)
  have hs2 : ∀ o, ({ w with outputData := o } : Writer .receiving).determineTransferMode = w.determineTransferMode :=
    fun _ => rfl
  cases ver <;> cases hs : w.determineTransferMode <;>
    simp only [Machine.writeHead, Machine.updateKeepAlive, Machine.disableKeepAlive, Machine.modifyWriter, TO,
      Message.Head.version, hs2, hs, ph_resp'] <;> rfl

theorem TO_writeFixedBody (n : Nat) :
    Writer.writeFixedBody { m.writer with outputData := O.append m.writer.outputData } n =
      ({ (Writer.writeFixedBody m.writer n).1 with
        outputData := O.append (Writer.writeFixedBody m.writer n).1.outputData }, (Writer.writeFixedBody m.writer n).2) := by
  by_cases h0 : m.writer.userData.size = 0
  · simp [Writer.writeFixedBody, h0]
  · simp [Writer.writeFixedBody, h0, ChunkedBuffer.append, Array.append_assoc, Nat.add_assoc]

theorem TO_writeChunkedBody :
    TO O (m.modifyWriter Writer.writeChunkedBody) = (TO O m).modifyWriter Writer.writeChunkedBody := by
  unfold TO Machine.modifyWriter Writer.writeChunkedBody
  dsimp only
  split
  · rfl
  · congr 2
    exact (ph_afoldl (fun b c => Encode.encode (v := .v11) b c) (fun c => ph_chunk c) _ O _).symm

theorem TO_writeRawBody :
    TO O (m.modifyWriter Writer.writeRawBody) = (TO O m).modifyWriter Writer.writeRawBody := by
  unfold TO Machine.modifyWriter Writer.writeRawBody
  dsimp only
  congr 2
  exact (ph_afoldl (fun buf (c : Chunk) => buf.write c.data) (fun c => ph_write c.data) _ O _).symm

theorem TO_writeFinalChunk :
    TO O (m.modifyWriter Writer.writeFinalChunk) = (TO O m).modifyWriter Writer.writeFinalChunk := by
  unfold TO Machine.modifyWriter Writer.writeFinalChunk Writer.writeChunkedBody
  dsimp only
  split
  · simp only [ChunkedBuffer.write, ChunkedBuffer.push, ChunkedBuffer.append, Array.append_push, Nat.add_assoc]
  · have := ph_afoldl (fun b c => Encode.encode (v := .v11) b c) (fun c => ph_chunk c)
      (m.writer.userData.filter (fun c => !c.data.isEmpty)) O m.writer.outputData
    simp only at this
    rw [this]
    simp only [ChunkedBuffer.write, ChunkedBuffer.push, ChunkedBuffer.append, Array.append_push, Nat.add_assoc]

theorem TO_omit :
    TO O (m.modifyWriter ({ · with userData := #[], userDataBytes := 0 })) =
      (TO O m).modifyWriter ({ · with userData := #[], userDataBytes := 0 }) := rfl

end

section
variable (O : ChunkedBuffer)

theorem to_completeStep (x : Machine .receiving) : TO O x.processCompleteStep = (TO O x).processCompleteStep := by
  unfold Machine.processCompleteStep
  by_cases h1 : x.isReaderComplete = true
  · have h1' : (TO O x).isReaderComplete = true := h1
    rw [if_pos h1, if_pos h1']
    by_cases h2 : x.keepAlive = true
    · have h2' : (TO O x).keepAlive = true := h2
      rw [if_pos h2, if_pos h2']
      exact TO_reset O x
    · have h2' : ¬ (TO O x).keepAlive = true := h2
      rw [if_neg h2, if_neg h2']; rfl
  · have h1' : ¬ (TO O x).isReaderComplete = true := h1
    rw [if_neg h1, if_neg h1']
    by_cases h3 : x.isReaderClosed = true
    · have h3' : (TO O x).isReaderClosed = true := h3
      rw [if_pos h3, if_pos h3']; rfl
    · have h3' : ¬ (TO O x).isReaderClosed = true := h3
      rw [if_neg h3, if_neg h3']
      by_cases h4 : x.isReaderAwaitingContinue = true
      · have h4' : (TO O x).isReaderAwaitingContinue = true := by rw [TO_isReaderAwaitingContinue]; exact h4
        rw [if_pos h4, if_pos h4']; rfl
      · have h4' : ¬ (TO O x).isReaderAwaitingContinue = true := by rw [TO_isReaderAwaitingContinue]; exact h4
        rw [if_neg h4, if_neg h4']
        by_cases h5 : x.keepAlive = true
        · have h5' : (TO O x).keepAlive = true := h5
          rw [if_pos h5, if_pos h5']
        · have h5' : ¬ (TO O x).keepAlive = true := h5
          rw [if_neg h5, if_neg h5']; rfl

theorem to_completeWriterMessage (x : Machine .receiving) :
    TO O x.completeWriterMessage = (TO O x).completeWriterMessage := by
  rw [Machine.completeWriterMessage, Machine.completeWriterMessage, ← TO_setWriterState]
  rw [(processWrite_cases _).1 rfl, (processWrite_cases _).1 rfl]
  exact to_completeStep O _

theorem to_completeOmittedBody (x : Machine .receiving) :
    TO O x.completeOmittedBody = (TO O x).completeOmittedBody := by
  rw [Machine.completeOmittedBody, Machine.completeOmittedBody, ← TO_omit]
  exact to_completeWriterMessage O _

theorem to_fixedBody (x : Machine .receiving) (n : Nat) :
    TO O (x.processFixedBody n) = (TO O x).processFixedBody n := by
  unfold Machine.processFixedBody
  by_cases h1 : x.writer.omitBody = true
  · have h1' : (TO O x).writer.omitBody = true := h1
    rw [if_pos h1, if_pos h1']; exact to_completeOmittedBody O x
  have h1' : ¬ (TO O x).writer.omitBody = true := h1
  rw [if_neg h1, if_neg h1']
  by_cases h2 : n = 0
  · rw [if_pos h2, if_pos h2]
    unfold Machine.processFixedZeroBody
    by_cases h3 : x.writer.userData.isEmpty = true
    · have h3' : (TO O x).writer.userData.isEmpty = true := h3
      rw [if_pos h3, if_pos h3']
      by_cases h4 : x.writer.userClosedBody = true
      · have h4' : (TO O x).writer.userClosedBody = true := h4
        rw [if_pos h4, if_pos h4']; exact to_completeWriterMessage O x
      · have h4' : ¬ (TO O x).writer.userClosedBody = true := h4
        rw [if_neg h4, if_neg h4']
    · have h3' : ¬ (TO O x).writer.userData.isEmpty = true := h3
      rw [if_neg h3, if_neg h3']; exact TO_closeOnBadMessage O x
  rw [if_neg h2, if_neg h2]
  by_cases h5 : x.writer.userData.size > 0
  · have h5' : (TO O x).writer.userData.size > 0 := h5
    rw [if_pos h5, if_pos h5']
    unfold Machine.processFixedBufferedBody
    by_cases h6 : Machine.bufferedUserDataBytes x.writer > n
    · have h6' : Machine.bufferedUserDataBytes (TO O x).writer > n := h6
      rw [if_pos h6, if_pos h6']; exact TO_closeOnBadMessage O x
    have h6' : ¬ Machine.bufferedUserDataBytes (TO O x).writer > n := h6
    rw [if_neg h6, if_neg h6']
    by_cases h7 : Machine.bufferedUserDataBytes x.writer = n ∧ (!x.writer.userClosedBody) = true
    · have h7' : Machine.bufferedUserDataBytes (TO O x).writer = n ∧ (!(TO O x).writer.userClosedBody) = true := h7
      rw [if_pos h7, if_pos h7']
    have h7' : ¬ (Machine.bufferedUserDataBytes (TO O x).writer = n ∧ (!(TO O x).writer.userClosedBody) = true) := h7
    rw [if_neg h7, if_neg h7']
    show TO O (let (writer, remaining) := Writer.writeFixedBody x.writer n
        let machine := { x with writer }
        let writer := machine.writer
        if remaining = 0 then
          if writer.userData.isEmpty then
            if writer.userClosedBody then machine.completeWriterMessage else machine.setWriterState (.writingBodyFixed 0)
          else machine.closeOnBadMessage
        else machine.setWriterState (.writingBodyFixed remaining)) =
      (let (writer, remaining) := Writer.writeFixedBody (TO O x).writer n
        let machine := { TO O x with writer }
        let writer := machine.writer
        if remaining = 0 then
          if writer.userData.isEmpty then
            if writer.userClosedBody then machine.completeWriterMessage else machine.setWriterState (.writingBodyFixed 0)
          else machine.closeOnBadMessage
        else machine.setWriterState (.writingBodyFixed remaining))
    have hw : (TO O x).writer = { x.writer with outputData := O.append x.writer.outputData } := rfl
    rw [hw, TO_writeFixedBody]
    obtain ⟨w', rem⟩ := Writer.writeFixedBody x.writer n
    have e2 : ({ TO O x with writer := { w' with outputData := O.append w'.outputData } } : Machine .receiving) =
        TO O { x with writer := w' } := rfl
    simp only [e2]
    by_cases h8 : rem = 0
    · simp only [h8, ↓reduceIte]
      by_cases h9 : w'.userData.isEmpty = true
      · simp only [h9, ↓reduceIte]
        by_cases h10 : w'.userClosedBody = true
        · simp only [h10, ↓reduceIte]; exact to_completeWriterMessage O _
        · simp only [h10, Bool.false_eq_true, ↓reduceIte]; exact (TO_setWriterState O _ _).symm
      · simp only [h9, Bool.false_eq_true, ↓reduceIte]; exact TO_closeOnBadMessage O _
    · simp only [h8, ↓reduceIte]; exact (TO_setWriterState O _ _).symm
  · have h5' : ¬ (TO O x).writer.userData.size > 0 := h5
    rw [if_neg h5, if_neg h5']
    unfold Machine.processFixedIdleBody
    by_cases h6 : x.writer.userClosedBody = true
    · have h6' : (TO O x).writer.userClosedBody = true := h6
      rw [if_pos h6, if_pos h6']; exact TO_closeOnBadMessage O x
    · have h6' : ¬ (TO O x).writer.userClosedBody = true := h6
      rw [if_neg h6, if_neg h6']


theorem to_chunkedBody_empty (x : Machine .receiving) (h0 : ¬ x.writer.userData.size > 0) :
    TO O x.processChunkedBody = (TO O x).processChunkedBody := by
  rw [Machine.processChunkedBody, Machine.processChunkedBody]
  by_cases h1 : x.writer.omitBody = true
  · have h1' : (TO O x).writer.omitBody = true := h1
    rw [if_pos h1, if_pos h1']; exact to_completeOmittedBody O x
  have h1' : ¬ (TO O x).writer.omitBody = true := h1
  rw [if_neg h1, if_neg h1']
  by_cases h2 : x.writer.userClosedBody = true
  · have h2' : (TO O x).writer.userClosedBody = true := h2
    rw [if_pos h2, if_pos h2', ← TO_writeFinalChunk]; exact to_completeWriterMessage O _
  have h2' : ¬ (TO O x).writer.userClosedBody = true := h2
  have h0' : ¬ (TO O x).writer.userData.size > 0 := h0
  rw [if_neg h2, if_neg h2', dif_neg h0, dif_neg h0']

theorem to_chunkedBody (x : Machine .receiving) (hs : x.writer.state = .writingBodyChunked) :
    TO O x.processChunkedBody = (TO O x).processChunkedBody := by
  refine (Classical.em (x.writer.userData.size > 0)).elim (fun h0 => ?_)
    (fun h0 => to_chunkedBody_empty O x h0)
  rw [Machine.processChunkedBody, Machine.processChunkedBody]
  by_cases h1 : x.writer.omitBody = true
  · have h1' : (TO O x).writer.omitBody = true := h1
    rw [if_pos h1, if_pos h1']; exact to_completeOmittedBody O x
  have h1' : ¬ (TO O x).writer.omitBody = true := h1
  rw [if_neg h1, if_neg h1']
  by_cases h2 : x.writer.userClosedBody = true
  · have h2' : (TO O x).writer.userClosedBody = true := h2
    rw [if_pos h2, if_pos h2', ← TO_writeFinalChunk]; exact to_completeWriterMessage O _
  have h2' : ¬ (TO O x).writer.userClosedBody = true := h2
  have h0' : (TO O x).writer.userData.size > 0 := h0
  rw [if_neg h2, if_neg h2', dif_pos h0, dif_pos h0', ← TO_writeChunkedBody]
  obtain ⟨h1', h2'⟩ := Machine.writeChunkedBody_spec x.writer h0
  have hs' : (x.modifyWriter Writer.writeChunkedBody).writer.state = .writingBodyChunked := by
    simp [Machine.modifyWriter, h2', hs]
  have hs'' : (TO O (x.modifyWriter Writer.writeChunkedBody)).writer.state = .writingBodyChunked := hs'
  rw [(processWrite_cases _).2.2.2.1 hs', (processWrite_cases _).2.2.2.1 hs'']
  exact to_chunkedBody_empty O _ (by show ¬ (Writer.writeChunkedBody x.writer).userData.size > 0; omega)

theorem to_closingFrame_empty (x : Machine .receiving) (h0 : ¬ x.writer.userData.size > 0) :
    TO O x.processClosingFrameBody = (TO O x).processClosingFrameBody := by
  rw [Machine.processClosingFrameBody, Machine.processClosingFrameBody]
  by_cases h1 : x.writer.omitBody = true
  · have h1' : (TO O x).writer.omitBody = true := h1
    rw [if_pos h1, if_pos h1']; exact to_completeOmittedBody O x
  have h1' : ¬ (TO O x).writer.omitBody = true := h1
  rw [if_neg h1, if_neg h1']
  by_cases h2 : x.writer.userClosedBody = true
  · have h2' : (TO O x).writer.userClosedBody = true := h2
    rw [if_pos h2, if_pos h2', ← TO_writeRawBody]; exact to_completeWriterMessage O _
  have h2' : ¬ (TO O x).writer.userClosedBody = true := h2
  have h0' : ¬ (TO O x).writer.userData.size > 0 := h0
  rw [if_neg h2, if_neg h2', if_neg h0, if_neg h0']

theorem to_closingFrame (x : Machine .receiving) (hs : x.writer.state = .writingBodyClosingFrame) :
    TO O x.processClosingFrameBody = (TO O x).processClosingFrameBody := by
  refine (Classical.em (x.writer.userData.size > 0)).elim (fun h0 => ?_)
    (fun h0 => to_closingFrame_empty O x h0)
  rw [Machine.processClosingFrameBody, Machine.processClosingFrameBody]
  by_cases h1 : x.writer.omitBody = true
  · have h1' : (TO O x).writer.omitBody = true := h1
    rw [if_pos h1, if_pos h1']; exact to_completeOmittedBody O x
  have h1' : ¬ (TO O x).writer.omitBody = true := h1
  rw [if_neg h1, if_neg h1']
  by_cases h2 : x.writer.userClosedBody = true
  · have h2' : (TO O x).writer.userClosedBody = true := h2
    rw [if_pos h2, if_pos h2', ← TO_writeRawBody]; exact to_completeWriterMessage O _
  have h2' : ¬ (TO O x).writer.userClosedBody = true := h2
  have h0' : (TO O x).writer.userData.size > 0 := h0
  rw [if_neg h2, if_neg h2', if_pos h0, if_pos h0', ← TO_writeRawBody]
  have hs' : (x.modifyWriter Writer.writeRawBody).writer.state = .writingBodyClosingFrame := by
    simp [Machine.modifyWriter, Writer.writeRawBody, hs]
  have hs'' : (TO O (x.modifyWriter Writer.writeRawBody)).writer.state = .writingBodyClosingFrame := hs'
  rw [(processWrite_cases _).2.2.2.2.1 hs', (processWrite_cases _).2.2.2.2.1 hs'']
  exact to_closingFrame_empty O _ (by simp [Machine.modifyWriter, Writer.writeRawBody])

theorem to_writing (x : Machine .receiving)
    (hs : x.writer.state = .writingBodyChunked ∨ x.writer.state = .writingBodyClosingFrame ∨
      ∃ n, x.writer.state = .writingBodyFixed n) :
    TO O x.processWrite = (TO O x).processWrite := by
  rcases hs with hs | hs | ⟨n, hs⟩
  · have hs' : (TO O x).writer.state = .writingBodyChunked := hs
    rw [(processWrite_cases x).2.2.2.1 hs, (processWrite_cases _).2.2.2.1 hs']
    exact to_chunkedBody O x hs
  · have hs' : (TO O x).writer.state = .writingBodyClosingFrame := hs
    rw [(processWrite_cases x).2.2.2.2.1 hs, (processWrite_cases _).2.2.2.2.1 hs']
    exact to_closingFrame O x hs
  · have hs' : (TO O x).writer.state = .writingBodyFixed n := hs
    rw [(processWrite_cases x).2.2.1 n hs, (processWrite_cases _).2.2.1 n hs']
    exact to_fixedBody O x n

/-- **The write loop with output in front** is the write loop with the output in front. -/
theorem pw_TO (x : Machine .receiving) : (TO O x).processWrite = TO O x.processWrite := by
  symm
  cases hs : x.writer.state with
  | pending =>
    have hs' : (TO O x).writer.state = .pending := hs
    rw [(processWrite_cases x).2.2.2.2.2.2.1 hs, (processWrite_cases _).2.2.2.2.2.2.1 hs']
    by_cases h1 : x.reader.isClosed = true
    · have h1' : (TO O x).reader.isClosed = true := h1
      rw [if_pos h1, if_pos h1']; exact TO_closeWriter O x
    · have h1' : ¬ (TO O x).reader.isClosed = true := h1
      rw [if_neg h1, if_neg h1']
  | waitingHeaders =>
    have hs' : (TO O x).writer.state = .waitingHeaders := hs
    rw [(processWrite_cases x).2.2.2.2.2.2.2 hs, (processWrite_cases _).2.2.2.2.2.2.2 hs']
    by_cases h1 : (!x.writer.sentMessage && x.writer.userClosedBody) = true
    · have h1' : (!(TO O x).writer.sentMessage && (TO O x).writer.userClosedBody) = true := h1
      rw [if_pos h1, if_pos h1']; exact TO_closeOnBadMessage O x
    · have h1' : ¬ (!(TO O x).writer.sentMessage && (TO O x).writer.userClosedBody) = true := h1
      rw [if_neg h1, if_neg h1']
  | waitingForFlush =>
    have hs' : (TO O x).writer.state = .waitingForFlush := hs
    rw [(processWrite_cases x).2.2.2.2.2.1 hs, (processWrite_cases _).2.2.2.2.2.1 hs']
    by_cases h1 : x.shouldFlush = true
    · have h1' : (TO O x).shouldFlush = true := h1
      rw [if_pos h1, if_pos h1']
      have hm : (TO O x).writer.messageHead = x.writer.messageHead := rfl
      rw [hm, ← TO_writeHead]
      exact to_writing O _ (writeHead_state' _ _)
    · have h1' : ¬ (TO O x).shouldFlush = true := h1
      rw [if_neg h1, if_neg h1']
  | writingBodyFixed n => exact to_writing O x (Or.inr (Or.inr ⟨n, hs⟩))
  | writingBodyChunked => exact to_writing O x (Or.inl hs)
  | writingBodyClosingFrame => exact to_writing O x (Or.inr (Or.inl hs))
  | complete =>
    have hs' : (TO O x).writer.state = .complete := hs
    rw [(processWrite_cases x).1 hs, (processWrite_cases _).1 hs']
    exact to_completeStep O x
  | closed =>
    have hs' : (TO O x).writer.state = .closed := hs
    rw [(processWrite_cases x).2.1 hs, (processWrite_cases _).2.1 hs']

end

/-! ## The read loop on the states after a pull -/

section
variable (O : ChunkedBuffer) (m : Machine .receiving)

theorem TO_failOnFramingHeaders (fh : Bool) :
    (TO O m).failOnFramingHeaders fh = TO O (m.failOnFramingHeaders fh) := by
  unfold Machine.failOnFramingHeaders
  split <;> rfl

theorem TO_reconcile (hs : Option Body.Length) (fh : Bool) :
    (TO O m).reconcileOutgoingFraming hs fh = TO O (m.reconcileOutgoingFraming hs fh) := by
  unfold Machine.reconcileOutgoingFraming
  have hw : (TO O m).writer.knownSize = m.writer.knownSize := rfl
  rw [hw]
  split
  · split <;> rfl
  · exact TO_failOnFramingHeaders O m fh
  · rfl
  · exact TO_failOnFramingHeaders O m fh

theorem TO_maybeSuppress (msg : Protocol.H1.Message.Head Direction.receiving.swap) :
    (TO O m).maybeSuppressOutgoingBody msg = TO O (m.maybeSuppressOutgoingBody msg) := by
  unfold Machine.maybeSuppressOutgoingBody Machine.suppressOutgoingBody
  dsimp only
  have hr : (TO O m).reader = m.reader := rfl
  rw [hr]
  by_cases hc : Machine.responseMustNotHaveBody msg.status = true ∨ (m.reader.messageHead.method == Method.head) = true
  · simp only [hc, ↓reduceIte]; rfl
  · simp only [hc, ↓reduceIte]

theorem TO_send (msg : Protocol.H1.Message.Head Direction.receiving.swap) : (TO O m).send msg = TO O (m.send msg) := by
  unfold Machine.send
  have hw : (TO O m).isWaitingMessage = m.isWaitingMessage := rfl
  have hf : (TO O m).failed = m.failed := rfl
  rw [hw, hf]
  split
  · rfl
  · dsimp only
    split
    · unfold TO Machine.modifyWriter
      dsimp only
      rw [ph_msgHead']
    · have e : (TO O m).modifyWriter ({ · with messageHead := msg, sentMessage := true }) =
          TO O (m.modifyWriter ({ · with messageHead := msg, sentMessage := true })) := rfl
      rw [e, TO_reconcile, TO_maybeSuppress]
      have hf2 : ∀ x : Machine .receiving, (TO O x).failed = x.failed := fun _ => rfl
      rw [hf2]
      split <;> rfl

theorem TO_send' (msg : Response.Head) : (TO O m).send msg = TO O (m.send msg) := TO_send O m msg

theorem TO_handleReaderFailed (e : Error) : (TO O m).handleReaderFailed e = TO O (m.handleReaderFailed e) := by
  rw [HttpSpec.RealSegment.handleReaderFailed_eq, HttpSpec.RealSegment.handleReaderFailed_eq]
  have hc : (¬(TO O m).writer.sentMessage = true ∧ ¬(TO O m).writer.isClosed = true) ↔
      (¬m.writer.sentMessage = true ∧ ¬m.writer.isClosed = true) := Iff.rfl
  by_cases h : ¬m.writer.sentMessage = true ∧ ¬m.writer.isClosed = true
  · rw [if_pos h, if_pos (hc.2 h)]
    have e1 : ((TO O m).setWriterState .waitingHeaders).disableKeepAlive =
        TO O ((m.setWriterState .waitingHeaders).disableKeepAlive) := rfl
    rw [e1, TO_send']
    rfl
  · rw [if_neg h, if_neg (fun h' => h (hc.1 h'))]
    rfl

theorem TO_completeState : (TO O m).processReaderCompleteState = TO O m.processReaderCompleteState := by
  unfold Machine.processReaderCompleteState
  dsimp only
  have hk : (TO O m).keepAlive = m.keepAlive := rfl
  have hr : (TO O m).reader = m.reader := rfl
  simp only [hk, hr]
  split <;> rfl

end

/-! ## The bytes of the output -/

theorem foldl_bytes : ∀ (l : List _root_.ByteArray) (init : _root_.ByteArray),
    (l.foldl (· ++ ·) init).data.toList = init.data.toList ++ (l.map fun b => b.data.toList).flatten
  | [], init => by simp
  | b :: bs, init => by
    simp only [List.foldl_cons, List.map_cons, List.flatten_cons]
    rw [foldl_bytes bs (init ++ b), ByteArray.data_append, Array.toList_append, List.append_assoc]

theorem toByteArray_bytes (c : ChunkedBuffer) :
    c.toByteArray.data.toList = (c.data.toList.map fun b => b.data.toList).flatten := by
  unfold ChunkedBuffer.toByteArray
  split
  · next h =>
    obtain ⟨⟨l⟩, sz⟩ := c
    simp only [List.size_toArray] at h
    match l, h with
    | [x], _ => simp
    | [], h => simp at h
    | _ :: _ :: _, h => simp at h
  · rw [← Array.foldl_toList, foldl_bytes]
    have : (ByteArray.emptyWithCapacity c.size).data = #[] := Array.eq_empty_of_size_eq_zero rfl
    rw [this]; simp

theorem outBytes_append (O X : ChunkedBuffer) : outBytes (O.append X) = outBytes O ++ outBytes X := by
  unfold outBytes
  rw [toByteArray_bytes, toByteArray_bytes, toByteArray_bytes]
  simp [ChunkedBuffer.append]

end HttpSpec.RealLoop
