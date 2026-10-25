import Spec.Message
import Spec.FramingFacts

/-!
# Examples of request messages

Two requests that satisfy `Message.RequestBytes`: a `GET` with no body, and a `POST` with a chunked
body that decodes to `abc`. They show the message grammar is not empty.
-/

namespace HttpSpec.MessageExamples

open HttpSpec.Chunked HttpSpec.Framing HttpSpec.Strict HttpSpec.Message

/-- The head of `GET / HTTP/1.1` with one field, `Host: a`. -/
def getHead : Head :=
  { method := ascii "GET", target := ascii "/", major := 0x31, minor := 0x31,
    fields := [(ascii "Host", ascii "a")] }

example : RequestBytes (ascii "GET / HTTP/1.1\r\nHost: a\r\n\r\n") getHead [] := by
  refine ⟨ascii "GET / HTTP/1.1\r\nHost: a\r\n\r\n", [], .length 0, by simp, ?_, ?_, ⟨rfl, rfl⟩⟩
  · refine ⟨ascii "GET / HTTP/1.1\r\n", ascii "Host: a\r\n", by decide, ?_, ?_⟩
    · exact ⟨[], EmptyLines.nil, ⟨by decide, by decide⟩, by decide, by decide, by decide, by decide,
        by decide⟩
    · have h := FieldLines.snoc FieldLines.nil
        (show FieldLineNV (ascii "Host: a") (ascii "Host") (ascii "a") from
          ⟨[SP], [], by decide, ⟨by decide, by decide⟩, by decide, ⟨by decide, by decide, by decide⟩,
            by decide⟩)
      have e : [] ++ ascii "Host: a" ++ CRLF = ascii "Host: a\r\n" := by decide
      rw [e] at h
      exact h
  · have hte : getHead.values "transfer-encoding" = [] := by decide
    have hcl : getHead.values "content-length" = [] := by decide
    rw [hte, hcl]
    exact Assigns.none

/-- The head of `POST / HTTP/1.1` with one field, `Transfer-Encoding: chunked`. -/
def postHead : Head :=
  { method := ascii "POST", target := ascii "/", major := 0x31, minor := 0x31,
    fields := [(ascii "Transfer-Encoding", ascii "chunked")] }

theorem chunkedIsFinal_chunked : ChunkedIsFinal [ascii "chunked"] := by
  have h := chunkedIsFinal_of_plain (t := ascii "chunked") (b := []) (ps := [])
    ⟨by decide, by decide⟩ (by intro _ h; cases h) (by simp) (fun _ => rfl) (by simp)
    (by intro n hn; simp at hn; subst hn; unfold IsChunked; decide)
  simpa using h

example : RequestBytes
    (ascii "POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n0\r\n\r\n")
    postHead (ascii "abc") := by
  refine ⟨ascii "POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n",
    ascii "3\r\nabc\r\n0\r\n\r\n", .chunked, by decide, ?_, ?_, ?_⟩
  · refine ⟨ascii "POST / HTTP/1.1\r\n", ascii "Transfer-Encoding: chunked\r\n", by decide, ?_, ?_⟩
    · exact ⟨[], EmptyLines.nil, ⟨by decide, by decide⟩, by decide, by decide, by decide, by decide,
        by decide⟩
    · have h := FieldLines.snoc FieldLines.nil
        (show FieldLineNV (ascii "Transfer-Encoding: chunked") (ascii "Transfer-Encoding")
            (ascii "chunked") from
          ⟨[SP], [], by decide, ⟨by decide, by decide⟩, by decide, ⟨by decide, by decide, by decide⟩,
            by decide⟩)
      have e : [] ++ ascii "Transfer-Encoding: chunked" ++ CRLF =
          ascii "Transfer-Encoding: chunked\r\n" := by decide
      rw [e] at h
      exact h
  · have hte : postHead.values "transfer-encoding" = [ascii "chunked"] := by decide
    have h10 : postHead.http10 = false := by decide
    rw [hte, h10]
    exact Assigns.chunked (by simp) rfl chunkedIsFinal_chunked
  · refine ⟨ascii "3\r\nabc\r\n", ascii "0\r\n", ascii "\r\n", by decide, ?_, ?_, ?_⟩
    · have h := Message.Chunks.snoc Message.Chunks.nil
        (show ChunkSizeLineL (ascii "3\r\n") 3 from
          ⟨ascii "3", [], by decide, ⟨by decide, by decide⟩, by decide, ⟨[], rfl, by simp⟩⟩)
        (by decide) (show (ascii "abc").length = 3 by decide)
      have e : [] ++ ascii "3\r\n" ++ ascii "abc" ++ CRLF = ascii "3\r\nabc\r\n" := by decide
      rw [e] at h
      exact h
    · exact ⟨ascii "0", [], by decide, ⟨by decide, by decide⟩, by decide, ⟨[], rfl, by simp⟩⟩
    · exact ⟨[], by decide, by simp⟩

end HttpSpec.MessageExamples
