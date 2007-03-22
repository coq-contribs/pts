
  Variable A : Prop .
  Variable R : A->A->Prop. 


  Definition Rstar:A->A->Prop :=
     [x,y:A](P0:A->A->Prop)
             ((u:A)(P0 u u))
              ->((u:A)(v:A)(w:A)(R u v)->(P0 v w)->(P0 u w))->(P0 x y).

  Definition Rstar':A->A->Prop :=
      [x,y:A](P:A->A->Prop)
             (P x x)->((u:A)(R x u)->(Rstar u y)->(P x y))->(P x y).

  Definition coherence: A->A->Prop :=
        [x:A][y:A](P:Prop)((z:A)(Rstar x z)->(Rstar y z)->P)->P.



(* Les 2 hypotheses du Lemme de Newman *)

  Axiom Hyp1:(x:A)(P:A->Prop)((y:A)((z:A)(R y z)->(P z))->(P y))->(P x).
  Axiom Hyp2:(x:A)(y:A)(z:A)(R x y)->(R x z)->(coherence y z).  


(* Verification du lemme *)

  Lemma Rstar_reflexive: (x:A)(Rstar x x).
Proof [x:A][P0:A->A->Prop]
        [H:(u:A)(P0 u u)][_:(u:A)(v:A)(w:A)(R u v)->(P0 v w)->(P0 u w)](H x).

  Lemma Rstar_R: (x:A)(y:A)(z:A)(R x y)->(Rstar y z)->(Rstar x z).
Proof [x,y,z:A][t1:(R x y)] [t2:(P0:A->A->Prop)
          ((u:A)(P0 u u))
           ->((u:A)(v:A)(w:A)(R u v)->(P0 v w)->(P0 u w))->(P0 y z)]
      [P:A->A->Prop][h1:(u:A)(P u u)]
        [h2:(u:A)(v:A)(w:A)(R u v)->(P v w)->(P u w)]
         (h2 x y z t1 (t2 [a,a0:A](P a a0) h1 h2)).

  Lemma Rstar_transitive: (x:A)(y:A)(z:A)(Rstar x y)->(Rstar y z)->(Rstar x z).
Proof [x,y,z:A][h:(P0:A->A->Prop)
        ((u:A)(P0 u u))
         ->((u:A)(v:A)(w:A)(R u v)->(P0 v w)->(P0 u w))->(P0 x y)]
      (h [a,a0:A](Rstar a0 z)->(Rstar a z) [u:A][H:(Rstar u z)]H
        [u,v,w:A][t1:(R u v)][t2:(Rstar w z)->(Rstar v z)]
           [t3:(Rstar w z)](Rstar_R u v z t1 (t2 t3))).

  Lemma Rstar'_reflexive: (x:A)(Rstar' x x).
Proof [x:A][P:A->A->Prop][H:(P x x)][_:(u:A)(R x u)->(Rstar u x)->(P x x)]H.

  Lemma Rstar'_R: (x:A)(y:A)(z:A)(R x z)->(Rstar z y)->(Rstar' x y).
Proof [x,y,z:A][t1:(R x z)][t2:(Rstar z y)][P:A->A->Prop]
       [_:(P x x)][h2:(u:A)(R x u)->(Rstar u y)->(P x y)](h2 z t1 t2).

  Lemma Rstar'_Rstar:  (x:A)(y:A)(Rstar' x y)->(Rstar x y).
Proof [x,y:A][h:(P:A->A->Prop)
       (P x x)->((u:A)(R x u)->(Rstar u y)->(P x y))->(P x y)]
      (h [a,a0:A](Rstar a a0) (Rstar_reflexive x) [u:A](Rstar_R x u y)).

  Lemma Rstar_Rstar':  (x:A)(y:A)(Rstar x y)->(Rstar' x y).
Proof [x,y:A][h:(P0:A->A->Prop)
       ((u:A)(P0 u u))
        ->((u:A)(v:A)(w:A)(R u v)->(P0 v w)->(P0 u w))->(P0 x y)]
       (h Rstar' [u:A](Rstar'_reflexive u)
         [u,v,w:A][h1:(R u v)]
          [h2:(Rstar' v w)](Rstar'_R u w v h1 (Rstar'_Rstar v w h2))).

  Lemma coherence_intro : (x:A)(y:A)(z:A)(Rstar x z)->(Rstar y z)
                                ->(coherence x y).
Proof [x,y,z:A][H:(Rstar x z)][H0:(Rstar y z)][P:Prop]
          [H1:(z0:A)(Rstar x z0)->(Rstar y z0)->P](H1 z H H0).

  Lemma Rstar_coherence : (x:A)(y:A)(Rstar x y)->(coherence x y).
Proof [x,y:A][h:(Rstar x y)](coherence_intro x y y h (Rstar_reflexive y)).

  Lemma coherence_sym: (x:A)(y:A)(coherence x y)->(coherence y x).
Proof [x,y:A][H:(P:Prop)((z:A)(Rstar x z)->(Rstar y z)->P)->P][P:Prop]
      [H0:(z:A)(Rstar y z)->(Rstar x z)->P]
       (H P [z:A][H1:(Rstar x z)][H2:(Rstar y z)](H0 z H2 H1)).

  Lemma Diagram:
   (x:A)((u:A)(R x u)->(y:A)(z:A)(Rstar u y)->(Rstar u z)->(coherence y z))
     ->(y,z,u:A)(R x u)->(Rstar u y)
           ->(v:A)(R x v)->(Rstar v z)->(coherence y z).
Proof [x:A][hyp_ind:(u:A)(R x u)->(y:A)(z:A)(Rstar u y)->(Rstar u z)
                      ->(coherence y z)]
     [y,z,u:A][t1:(R x u)][t2:(Rstar u y)][v:A][u1:(R x v)][u2:(Rstar v z)]
        ([Hyp0:(x0,y0,z0:A)(R x0 y0)->(R x0 z0)
                    ->(P:Prop)((z1:A)(Rstar y0 z1)->(Rstar z0 z1)->P)->P]
             [hyp_ind0:(u0:A)(R x u0)->(y0,z0:A)(Rstar u0 y0)->(Rstar u0 z0)
                        ->(P:Prop)((z1:A)(Rstar y0 z1)->(Rstar z0 z1)->P)->P]
              (Hyp0 x u v t1 u1 (coherence y z)
                [z0:A][H:(Rstar u z0)][H0:(Rstar v z0)]
                   (hyp_ind0 u t1 y z0 t2 H (coherence y z)
                     [z1:A][H1:(Rstar y z1)][H2:(Rstar z0 z1)]
                        (hyp_ind0 v u1 z z1 u2
                          (Rstar_transitive v z0 z1 H0 H2)
                          (coherence y z)
                          [z2:A][H3:(Rstar z z2)][H4:(Rstar z1 z2)]
                            [P:Prop][H5:(z3:A)(Rstar y z3)->(Rstar z z3)->P]
                                (H5 z2
                                  (Rstar_transitive y z1 z2 H1 H4) H3))))
            Hyp2 hyp_ind).

  Lemma caseRxy:
    (x:A)((u:A)(R x u)->(y,z:A)(Rstar u y)->(Rstar u z)->(coherence y z))
        ->(y,z:A)(Rstar x y)->(Rstar x z)
                ->(u:A)(R x u)->(Rstar u y)->(coherence y z).
Proof [x:A][hyp_ind:(u:A)
           (R x u)->(y:A)(z:A)(Rstar u y)->(Rstar u z)->(coherence y z)]
  [y,z:A][h1:(Rstar x y)][h2:(Rstar x z)][u:A][t1:(R x u)][t2:(Rstar u y)]
        ([hyp_:(P:A->A->Prop)(P x x)
                  ->((u0:A)(R x u0)->(Rstar u0 z)->(P x z))->(P x z)]
           (hyp_ [_:A][a:A](coherence y a)
             (coherence_sym x y (Rstar_coherence x y h1))
             (Diagram x hyp_ind y z u t1 t2))
          (Rstar_Rstar' x z h2)).

  Lemma Ind_proof :
    (x:A)((u:A)(R x u)->(y:A)(z:A)(Rstar u y)->(Rstar u z)->(coherence y z))
            ->(y:A)(z:A)(Rstar x y)->(Rstar x z)->(coherence y z).
Proof [x:A][hyp_ind:(u:A)
           (R x u)->(y:A)(z:A)(Rstar u y)->(Rstar u z)->(coherence y z)]
  [y,z:A][h1:(Rstar x y)][h2:(Rstar x z)]
     ([hyp_:(P:A->A->Prop)
              (P x x)->((u:A)(R x u)->(Rstar u y)->(P x y))->(P x y)]
        (hyp_ [_:A][a:A](coherence a z) (Rstar_coherence x z h2)
          (caseRxy x hyp_ind y z h1 h2))
       (Rstar_Rstar' x y h1)).

  Lemma Newman: (x:A)(y:A)(z:A)(Rstar x y)->(Rstar x z)->(coherence y z).
Proof [x:A](Hyp1 x
   [x:A](y:A)(z:A)(Rstar x y)->(Rstar x z)->(coherence y z) Ind_proof).


Quit.
