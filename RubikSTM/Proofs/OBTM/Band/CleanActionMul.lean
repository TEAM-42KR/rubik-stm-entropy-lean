import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false
open Rubik RubikOBTM RubikOBTM.Band
set_option maxHeartbeats 600000

theorem proof_RubikOBTM_Band_clean_action_mul {n : ℕ} (a u v : Fin n) (p q : PairPerm)
    (P Q : Equiv.Perm (Sticker n)) (hp : CleanAction a u v p P)
    (hq : CleanAction a u v q Q) : CleanAction a u v (p*q) (P*Q) := by
  constructor
  · intro d hd i
    constructor
    · change P (Q (plus a d i)) = plus a d (p.1 (q.1 i))
      rw [(hq.1 d hd i).1, (hp.1 d hd (q.1 i)).1]
    · change P (Q (minus a d i)) = minus a d (p.2 (q.2 i))
      rw [(hq.1 d hd i).2, (hp.1 d hd (q.2 i)).2]
  · intro s hs
    change P (Q s) = s
    rw [hq.2 s hs, hp.2 s hs]
