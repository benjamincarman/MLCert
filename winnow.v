Require Import MLCert.monads MLCert.axioms MLCert.float32.

Section Winnow.
  Variable n: nat. (*dimensionality*)
  Notation X := (float32_arr n).
  Notation Y := bool.
  Context {training_set} `{Foldable training_set (X*Y)}.

  (*Q: Maybe define this by folding over training set?*)
  Variable rho: float32. (*Max feature in any of examples after absolute value*)
  Variable epsilon: float32. (*Predetermined constant in range 0 to 1*)
  
Open Scope f32_scope.

  Definition eta: float32 := epsilon / (2 * rho).
  
  Variable T: training_set.

  Section WeightVector.
    (*Previous weight vector*)
    Variable w: float32_arr n.
    Variable c: float32_arr n.

    (*Return previous weight vector where each element *= (1.0-eta*cost_vector)*)
    Definition weight_vector: float32_arr n :=
      f32_map2 (fun c w => (f32_1 + (neg1 * eta * c)) * w) c w.
  End WeightVector.


  Section CostVector.
    Variable w: float32_arr n.
    
    Definition violates (xy: X*Y): bool :=
      let: (x,y) := xy in 0 > float32_of_bool y * f32_dot x w.
    
    (*How does this relate back to training set T?
      Is it through function foldable_foldM?*)
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