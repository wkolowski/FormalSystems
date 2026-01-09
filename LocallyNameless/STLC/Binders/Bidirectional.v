(*
Inductive Infer : Ctx -> Tm -> Ty -> Prop :=
| Infer_fvar :
  forall (Γ : Ctx) (x : Atom) (A : Ty)
    (HB : Binds Γ x A),
    Infer Γ x A
| Infer_app  :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty)
    (Hi1 : Infer Γ t1 (TyFun A B))
    (Hc2 : Check Γ t2 A),
    Infer Γ (app t1 t2) B
| Infer_annot :
  forall (Γ : Ctx) (t : Tm) (A : Ty)
    (Hc' : Check Γ t A),
    Infer Γ (annot t A) A
| Infer_unit :
  forall (Γ : Ctx),
    Infer Γ unit TyUnit
| Infer_elimUnit :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty) (l : list Atom)
    (Hc1 : Check Γ t1 TyUnit)
    (Hi2 : forall x : Atom, x # l -> Infer ((x, TyUnit) :: Γ) (t2 {{ 0 ~> x }}) A),
    Infer Γ (elimUnit t1 t2) A
| Infer_pair :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty)
    (Hi1 : Infer Γ t1 A)
    (Hi2 : Infer Γ t2 B),
    Infer Γ (pair t1 t2) (TyProd A B)
| Infer_outl :
  forall (Γ : Ctx) (t : Tm) (A B : Ty)
    (Hi : Infer Γ t (TyProd A B)),
    Infer Γ (outl t) A
| Infer_outr :
  forall (Γ : Ctx) (t : Tm) (A B : Ty)
    (Hi : Infer Γ t (TyProd A B)),
    Infer Γ (outr t) B
| Infer_elimProd :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B C : Ty) (l : list Atom)
    (Hi1 : Infer Γ t1 (TyProd A B))
    (Hi2 : forall x y : Atom, x # l -> y # x :: l ->
      Infer ((y, B) :: (x, A) :: Γ) (t2 {{ 0 ~> x }} {{ 1 ~> y }}) C),
    Infer Γ (elimProd t1 t2) C
| Infer_case :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C1 C2 : Ty) (l : list Atom)
    (Hi1 : Infer Γ t1 (TySum A B))
    (Hi2 : forall x : Atom, x # l -> Infer ((x, A) :: Γ) (t2 {{ 0 ~> x }}) C1)
    (Hi3 : forall x : Atom, x # l -> Infer ((x, B) :: Γ) (t3 {{ 0 ~> x }}) C2)
    (Heq : C1 = C2),
    Infer Γ (case t1 t2 t3) C1
| Infer_case_asym :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C : Ty) (l : list Atom)
    (Hi1 : Infer Γ t1 (TySum A B))
    (Hi2 : forall x : Atom, x # l -> Infer ((x, A) :: Γ) (t2 {{ 0 ~> x }}) C)
    (Hc3 : forall x : Atom, x # l -> Check ((x, B) :: Γ) (t3 {{ 0 ~> x }}) C),
    Infer Γ (case t1 t2 t3) C
| Infer_zero :
  forall (Γ : Ctx),
    Infer Γ zero TyNat
| Infer_succ :
  forall (Γ : Ctx) (t : Tm)
    (Hc' : Check Γ t TyNat),
    Infer Γ (succ t) TyNat

with Check : Ctx -> Tm -> Ty -> Prop :=
| Check_Infer :
  forall (Γ : Ctx) (t : Tm) (A : Ty)
    (Hi : Infer Γ t A),
    Check Γ t A
| Check_abs :
  forall (Γ : Ctx) (t : Tm) (A B : Ty) (l : list Atom)
    (Hc : forall x : Atom, x # l -> Check ((x, A) :: Γ) (t {{0 ~> x}}) B),
    Check Γ (abs t) (TyFun A B)
| Check_elimUnit' :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty)
    (Hc1 : Check Γ t1 TyUnit)
    (Hc2 : Check Γ t2 (TyFun TyUnit A)),
    Check Γ (elimUnit' t1 t2) A
| Check_elimUnit'' :
  forall (Γ : Ctx) (A : Ty),
    Check Γ elimUnit'' (TyFun (TyFun TyUnit A) (TyFun TyUnit A))
| Check_abort :
  forall (Γ : Ctx) (t' : Tm) (A : Ty)
    (Hc : Check Γ t' TyEmpty),
    Check Γ (abort t') A
| Check_pair :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty)
    (Hc1 : Check Γ t1 A)
    (Hc2 : Check Γ t2 B),
    Check Γ (pair t1 t2) (TyProd A B)
| Check_inl :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty)
    (Hc : Check Γ t' A),
    Check Γ (inl t') (TySum A B)
| Check_inr :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty)
    (Hc : Check Γ t' B),
    Check Γ (inr t') (TySum A B)
| Check_case :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C : Ty) (l : list Atom)
    (Hi1 : Infer Γ t1 (TySum A B))
    (Hc2 : forall x : Atom, x # l -> Check ((x, A) :: Γ) (t2 {{ 0 ~> x }}) C)
    (Hc3 : forall x : Atom, x # l -> Check ((x, B) :: Γ) (t3 {{ 0 ~> x }}) C),
    Check Γ (case t1 t2 t3) C
| Check_case' :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C : Ty)
    (Hi3 : Infer Γ t3 (TySum A B))
    (Hc1 : Check Γ t1 (TyFun A C))
    (Hc2 : Check Γ t2 (TyFun B C)),
    Check Γ (case' t1 t2 t3) C
| Check_case'' :
  forall (Γ : Ctx) (A B C : Ty),
    Check Γ case'' (TyFun (TyFun A C) (TyFun (TyFun B C) (TyFun (TySum A B) C))).
*)
