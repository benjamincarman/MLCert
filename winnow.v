Require Import MLCert.monads MLCert.axioms MLCert.float32.

Section Winnow.
  Variable n: nat. (*dimensionality*)
  Notation X := (float32_arr n).
  Notation Y := bool.
  Context {training_set} `{Foldable training_set (X*Y)}.
  Variable rho: float32.

  Open Scope f32_scope.
  
  Variable T: training_set.
  
  Section CostVector.
    Variable w: float32_arr n.
    
    Definition violates (xy: X*Y): bool :=
      let: (x,y) := xy in 0 > float32_of_bool y * f32_dot x w.
    
    Definition find_violating: option (X*Y) :=
      foldable_foldM
        (M:=Id)
        (fun xy acc =>
           match acc with
           | None => if violates xy then ret (Some xy) else ret acc
           | Some first_violating => ret acc
           end)
        None T.

    Definition cost_vector: option (float32_arr n) :=
      match find_violating with
      | None => None
      | Some (x, y) =>
        Some (f32_map (fun x => (neg1 / rho) * float32_of_bool y * x) x)
      end.
  End CostVector.
End Winnow.  
           
      
    

  

  