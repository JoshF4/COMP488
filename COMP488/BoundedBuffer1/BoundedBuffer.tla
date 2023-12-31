-------------------------------- MODULE BoundedBuffer --------------------------------
EXTENDS Naturals, Integers, Sequences, TLC

CONSTANTS PROD,       \* number of producers 
          CONS,       \* number of consumers 
          BufferSize  \* buffer size
          
ASSUME /\ PROD > 0
       /\ CONS > 0
       /\ BufferSize > 0
       
put(buf,el) == Append(buf,el)
get(buf) == Tail(buf)

(*

--algorithm BoundedBuffer {
    variables \* running_threads={}, \* producers ready to work 
              \* wait_set={},        \* producers waiting on a full/empty buffer
              buff = <<>>,           \* buffer
              accesses=0;            \* total number of gets and puts
  
 
   process(p \in 1..PROD) {
      p0:
        while(accesses < 100) {
           either {
              p1:
                when Len(buf) < BufferSize;
                accesses := accesses +1;
                buf := Append(buf, accesses);
           }
           or {
              p2: skip;
           }
        };
   }
   
   process(c \in 5..CONS+5) {
      c0:
         while(accesses < 100) {
               either {
                  c1:
                    when Len(buf) > 0;
                    buf := Tail(buf);
                    accesses := accesses +1;
               }
               or {
                  c2: skip;
               }
         };
   } 
 

}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "bf99069a" /\ chksum(tla) = "ef4f4027")
VARIABLES buf, accesses, pc

vars == << buf, accesses, pc >>

ProcSet == (1..PROD) \cup (5..CONS+5)

Init == (* Global variables *)
        /\ buf = <<>>
        /\ accesses = 0
        /\ pc = [self \in ProcSet |-> CASE self \in 1..PROD -> "p0"
                                        [] self \in 5..CONS+5 -> "c0"]

p0(self) == /\ pc[self] = "p0"
            /\ IF accesses < 100
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "p1"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "p2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << buf, accesses >>

p1(self) == /\ pc[self] = "p1"
            /\ Len(buf) < BufferSize
            /\ accesses' = accesses +1
            /\ buf' = Append(buf, accesses')
            /\ pc' = [pc EXCEPT ![self] = "p0"]

p2(self) == /\ pc[self] = "p2"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "p0"]
            /\ UNCHANGED << buf, accesses >>

p(self) == p0(self) \/ p1(self) \/ p2(self)

c0(self) == /\ pc[self] = "c0"
            /\ IF accesses < 100
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "c1"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "c2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << buf, accesses >>

c1(self) == /\ pc[self] = "c1"
            /\ Len(buf) > 0
            /\ buf' = Tail(buf)
            /\ accesses' = accesses +1
            /\ pc' = [pc EXCEPT ![self] = "c0"]

c2(self) == /\ pc[self] = "c2"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "c0"]
            /\ UNCHANGED << buf, accesses >>

c(self) == c0(self) \/ c1(self) \/ c2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..PROD: p(self))
           \/ (\E self \in 5..CONS+5: c(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====


