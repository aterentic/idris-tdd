data DoorState = DoorClosed | DoorOpen

data DoorResult = OK | Jammed

-- data DoorCmd : Type -> DoorState -> DoorState -> Type where
--      Open : DoorCmd () DoorClosed DoorOpen
--      Close : DoorCmd () DoorOpen DoorClosed
--      RingBell : DoorCmd () a a
     
--      Pure : ty -> DoorCmd () state state
--      (>>=) : DoorCmd a s1 s2 -> (a -> DoorCmd b s2 s3) -> DoorCmd b s1 s3


data DoorCmd : (ty : Type) -> DoorState -> (ty -> DoorState) -> Type where
     Open : DoorCmd DoorResult DoorClosed
                               (\res => case res of
                               OK => DoorOpen
                               Jammed => DoorClosed)
     Close : DoorCmd () DoorOpen (const DoorClosed)
     RingBell : DoorCmd () DoorClosed (const DoorClosed)
     
     Display : String -> DoorCmd () state (const state)
     
     Pure : (res : ty) -> DoorCmd ty (state_fn res) state_fn
     (>>=) : DoorCmd a state1 state2_fn ->
             ((res : a) -> DoorCmd b (state2_fn res) state3_fn) ->
             DoorCmd b state1 state3_fn
       
-- doorProg : DoorCmd () DoorClosed DoorClosed
-- doorProg = do RingBell 
--               Open
--               RingBell
--               Close

doorProg : DoorCmd () DoorClosed (const DoorClosed)
doorProg = do RingBell
              OK <- Open | Jammed => Display "Door Jammed"
              Display "Glad To Be Of Service"
              Close

logOpen : DoorCmd DoorResult DoorClosed (\res => case res of
                                                      OK => DoorOpen
                                                      Jammed => DoorClosed)
logOpen = do Display "Trying to open the door"
             OK <- Open | Jammed => do Display "Jammed"
                                       Pure Jammed
             Display "Success"
             Pure OK

