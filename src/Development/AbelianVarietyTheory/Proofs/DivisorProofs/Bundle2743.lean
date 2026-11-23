module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam.LevAlg

variable {S : Scheme.{0}}

section Hom

variable {G H : Over S} [GrpObj G] [GrpObj H]

theorem isMonHom_of_mulComp (f : G ⟶ H)
    (h : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  refine ⟨?_, ?_⟩
  · rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ G ↦ x ≫ f) (h _))
  · simpa only [MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd] using
      h (G ⊗ G) (fst G G) (snd G G)

theorem isMonHom_mul [IsCommMonObj H] (f g : G ⟶ H) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) :=
  isMonHom_of_mulComp _ fun T x y ↦ by
    simp only [MonObj.comp_mul, MonObj.mul_comp]
    exact mul_mul_mul_comm _ _ _ _

theorem isMonHom_one : IsMonHom (1 : G ⟶ H) :=
  isMonHom_of_mulComp _ fun T x y ↦ by simp

theorem isMonHom_zpow [IsCommMonObj H] (f : G ⟶ H) [IsMonHom f] (n : ℤ) : IsMonHom (f ^ n) :=
  isMonHom_of_mulComp _ fun T x y ↦ by
    simp only [GrpObj.comp_zpow, MonObj.mul_comp, mul_zpow]

theorem isMonHom_prod [IsCommMonObj H] {K : Type} (s : Finset K) (f : K → (G ⟶ H))
    (hf : ∀ i, IsMonHom (f i)) : IsMonHom (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isMonHom_one : IsMonHom (1 : G ⟶ H))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    haveI := hf a
    exact isMonHom_mul _ _

end Hom

section Obj

variable (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem mkZ_pa {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  unfold mkZ pa
  rw [lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

theorem mkZ_pb {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  unfold mkZ pb
  rw [lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

theorem zob_ext {T : Over S} (f g : T ⟶ Zob A B) (ha : ∀ i, f ≫ pa A B i = g ≫ pa A B i)
    (hb : ∀ j, f ≫ pb A B j = g ≫ pb A B j) : f = g := by
  apply CartesianMonoidalCategory.hom_ext
  · apply (Out.powIsLimit A 4).hom_ext
    rintro ⟨i⟩
    simpa [pa] using ha i
  · apply (Out.powIsLimit B 4).hom_ext
    rintro ⟨j⟩
    simpa [pb] using hb j

instance isMonHom_pa (i : Fin 4) : IsMonHom (pa A B i) := by
  unfold pa; infer_instance

instance isMonHom_pb (j : Fin 4) : IsMonHom (pb A B j) := by
  unfold pb; infer_instance

theorem isMonHom_mkZ {T : Over S} [GrpObj T] (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B))
    (hu : ∀ i, IsMonHom (u i)) (hv : ∀ j, IsMonHom (v j)) : IsMonHom (mkZ A B u v) :=
  isMonHom_of_mulComp _ fun T' x y ↦ by
    apply zob_ext
    · intro i
      haveI := hu i
      simp only [Category.assoc, mkZ_pa, MonObj.mul_comp]
    · intro j
      haveI := hv j
      simp only [Category.assoc, mkZ_pb, MonObj.mul_comp]

theorem isMonHom_incZ : IsMonHom (incZ A B) := by
  unfold incZ
  apply isMonHom_mkZ
  · intro i
    split_ifs
    · infer_instance
    · exact isMonHom_one
  · intro j
    exact isMonHom_one

theorem isMonHom_actZ (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) [IsMonHom la] [IsMonHom mu] (N : ord d) :
    IsMonHom (actZ A B d la mu N) := by
  unfold actZ
  apply isMonHom_mkZ
  · intro i
    apply isMonHom_prod
    intro j
    haveI := isMonHom_zpow (pa A B j) ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inl j) (Sum.inl i))
    haveI := isMonHom_zpow (pb A B j ≫ mu)
      ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inr j) (Sum.inl i) / (d : ℤ))
    exact isMonHom_mul _ _
  · intro i
    apply isMonHom_prod
    intro j
    haveI := isMonHom_zpow (pa A B j ≫ la) ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inl j) (Sum.inr i))
    haveI := isMonHom_zpow (pb A B j) ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inr j) (Sum.inr i))
    exact isMonHom_mul _ _

end Obj

end GlobalTheory.ZarhinFam.LevAlg

namespace GlobalTheory.ZarhinFam.LevAlg

theorem levZ_add_tors : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → (∀ a b, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (a + b) = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a * (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) b) ∧ ∀ a, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a ^ M = 1 := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ _ _ _ _ κ _
  haveI : IsMonHom la := hZ.2.2.2.1
  haveI : IsMonHom mu := hZ.2.2.2.2.1
  have hg : ∀ k, IsMonHom (incZ c.A B ≫ actZ c.A B d la mu (oMat d k)) := fun k => by
    haveI := isMonHom_incZ c.A B
    haveI := isMonHom_actZ c.A B d la mu (oMat d k)
    infer_instance
  constructor
  · intro a b
    simp only [levZ, List.prod_ofFn]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    haveI := hg k
    rw [map_add (f := _), c.lev_add, MonObj.mul_comp]
  · intro a
    simp only [levZ, List.prod_ofFn]
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun k _ => ?_
    haveI := hg k
    rw [← MonObj.pow_comp, c.lev_tors]
    simp

end GlobalTheory.ZarhinFam.LevAlg
end
end

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt

set_option autoImplicit false

noncomputable section

open scoped TensorProduct




namespace GlobalTheory.UnframeForms

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ)

abbrev movedS : NX.RatDat D.ntw :=
  { S with
    A := fun n => moveForms (S.A n) fun σ => (YS.fi (NX.idxOf D n)).eG.symm (w (NX.idxOf D n) σ) }

def movedIso (i : Fin D.R.m) : NX.FormsIso ((movedS YS w).A ((i : ℕ) + 1)) ((fullHeckeRealDatMovedReadings Rl w).FW i) where
  eK := (YS.fi i).eK
  eK_LL := (YS.fi i).eK_LL
  e := (YS.fi i).e
  eG := (YS.fi i).eG
  eW := (YS.fi i).eW
  wk := (YS.fi i).wk
  mkK := (YS.fi i).mkK
  rho := (YS.fi i).rho
  chi := (YS.fi i).chi
  j σ x := by
    change (Rl.FW i).j σ ((Rl.FW i).ρ (w i σ) ((YS.fi i).e x)) =
      (YS.fi i).eW σ ((S.A _).j σ ((S.A _).ρ ((YS.fi (NX.idxOf D ((i : ℕ) + 1))).eG.symm
        (w (NX.idxOf D ((i : ℕ) + 1)) σ)) x))
    rw [NX.idxOf_succ, ← (YS.fi i).j, (YS.fi i).rho, MulEquiv.apply_symm_apply]

def movedYS : NX.NExpRealS (fullHeckeRealDatMovedReadings Rl w) cG (movedS YS w) where
  fi := movedIso YS w
  geq := YS.geq
  rho := YS.rho
  chi := YS.chi
  eF := YS.eF
  bsup := YS.bsup
  act := YS.act

variable (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem evW_moved (j : Fin D.R.m) (x : S.WL ((j : ℕ) + 1)) :
    evW (movedYS YS w) v₀ j x = evW YS v₀ j ((S.A ((j : ℕ) + 1)).ρ ((YS.fi j).eG.symm (w j (sg0 D A3.A))) x) := by
  change (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((Rl.FW j).ρ (w j (sg0 D A3.A)) ((YS.fi j).e x))) (v₀ j _) =
    (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e ((S.A _).ρ ((YS.fi j).eG.symm (w j (sg0 D A3.A))) x)))
      (v₀ j _)
  rw [(YS.fi j).rho, MulEquiv.apply_symm_apply]

theorem evK_moved {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    ∃ y, evK (movedYS YS w) v₀ hρ i j b x = evK YS v₀ hρ i j b y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, (map_zero _).trans (map_zero _).symm⟩
  | add x y hx hy =>
    obtain ⟨x', ex⟩ := hx
    obtain ⟨y', ey⟩ := hy
    exact ⟨x' + y', (map_add _ _ _).trans ((congrArg₂ (· + ·) ex ey).trans (map_add _ _ _).symm)⟩
  | tmul a f =>
    refine ⟨a ⊗ₜ (⟨(S.A ((j : ℕ) + 1)).ρ ((YS.fi j).eG.symm (w j (sg0 D A3.A))) (show ↥(S.A ((j : ℕ) + 1)).WK from f).1,
      YS.rho _ (Nat.le_add_left _ _) j.2 _ _ (show ↥(S.A ((j : ℕ) + 1)).WK from f).2⟩ : ↥(S.A ((j : ℕ) + 1)).WK), ?_⟩
    exact congrArg (ρ.e i b a • ·) (evW_moved YS w v₀ j _)

theorem realRd_moved {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ)
    (f : D.nexp.Fm i ((j : ℕ) + 1) b) :
    ∃ f', realRd (movedYS YS w) v₀ hρ i j b ν f = realRd YS v₀ hρ i j b ν f' := by
  obtain ⟨y, hy⟩ := evK_moved YS w v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)
  refine ⟨(YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y, ?_⟩
  change ν⁻¹ • evK (movedYS YS w) v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) =
    ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y))
  rw [hy]
  exact congrArg (fun z => ν⁻¹ • evK YS v₀ hρ i j b z)
    ((YS.eF i _ b (Nat.le_add_left _ _) j.2).apply_symm_apply (show NX.Fm S i ((j : ℕ) + 1) b from y)).symm

end GlobalTheory.UnframeForms

namespace GlobalTheory.UnframeForms

open GlobalTheory.ExportSeries

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X} (hρ : ρ.Good)
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw} {j : Fin D.R.m} {b : Bool} {rd rd' : Rd ρ Y i j b}

theorem rdK_sub (h : ∀ f, ∃ f', rd' f = rd f') (k : ℕ) (x : X.Ok i k ⊗[X.O i] Y.Fm i ((j : ℕ) + 1) b) :
    ∃ x', rdK rd' hρ k x = rdK rd hρ k x' := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, (map_zero _).trans (map_zero _).symm⟩
  | add x y hx hy =>
    obtain ⟨x', ex⟩ := hx
    obtain ⟨y', ey⟩ := hy
    exact ⟨x' + y', (map_add _ _ _).trans ((congrArg₂ (· + ·) ex ey).trans (map_add _ _ _).symm)⟩
  | tmul a f =>
    obtain ⟨f', e⟩ := h f
    exact ⟨a ⊗ₜ f', by rw [rdK_tmul, rdK_tmul, e]⟩

theorem rat_of_sub (h : ∀ f, ∃ f', rd' f = rd f') (h' : Rat hρ rd') : Rat hρ rd := by
  obtain ⟨h1, h2, h3⟩ := h'
  refine ⟨fun s g P hd => ?_, fun k Q ψ hk hQ s g P hd x hx => ?_, fun Q M hQ s g P hd hs a => ?_⟩
  · obtain ⟨f, hf⟩ := h1 s g P hd
    obtain ⟨f', e⟩ := h f
    exact ⟨f', e.symm.trans hf⟩
  · obtain ⟨y, hy⟩ := h2 k Q ψ hk hQ s g P hd hx
    obtain ⟨y', e⟩ := rdK_sub hρ h k y
    exact ⟨y', e.symm.trans hy⟩
  · obtain ⟨f, hf⟩ := h3 Q M hQ s g P hd hs a
    obtain ⟨f', e⟩ := h f
    exact ⟨f', e.symm.trans hf⟩

end GlobalTheory.UnframeForms

theorem GlobalTheory.UnframeForms.ratRow_back : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ), (∀ i σ, w i σ ∈ Subgroup.center Γ) → ∃ (S' : NX.RatDat D.ntw) (YS' : NX.NExpRealS (fullHeckeRealDatMovedReadings Rl w) cG S'), ∀ (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), RatRow YS' v₀ hρ i j b → RatRow YS v₀ hρ i j b :=
  fun Rl _ _ YS w _ => ⟨GlobalTheory.UnframeForms.movedS YS w, GlobalTheory.UnframeForms.movedYS YS w, fun v₀ _ hρ i j b ⟨ν, hn, hr⟩ =>
    ⟨ν, hn, GlobalTheory.UnframeForms.rat_of_sub hρ (GlobalTheory.UnframeForms.realRd_moved YS w v₀ hρ i j b ν) hr⟩⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProdPairing

open GlobalTheory.CechPic GlobalTheory.DiagPairing

section Theta

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {P : LB (A ⊗ A).left} (hP : P.IsLB)
  (hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y)
  (hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y')

include hB in
theorem pc_one_left {T : Over S} (y : T ⟶ A) : pc hP (1 : T ⟶ A) y = 0 := by
  have := hB T 1 1 y
  rwa [_root_.mul_one, left_eq_add] at this

include hB' in
theorem pc_one_right {T : Over S} (x : T ⟶ A) : pc hP x (1 : T ⟶ A) = 0 := by
  have := hB' T x 1 1
  rwa [_root_.mul_one, left_eq_add] at this


include hB hB' in
theorem exists_theta_prod {k : ℕ} {T : Over S} (X : T ⟶ G2 A) (hX : X ^ k = 1) :
    ∃ θ : Out.ThetaGrp (G2 A) P k T, θ.pt = X := by
  have e : ∀ g : T ⊗ G2 A ⟶ G2 A, pull g.left (cls P hP) = pc hP (g ≫ fst A A) (g ≫ snd A A) := fun g => by
    unfold pc
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  have tr : Out.translPt (G2 A) X = (fst T (G2 A) ≫ X) * snd T (G2 A) := rfl
  have h₁ : (fst T (G2 A) ≫ X ≫ fst A A) ^ k = 1 := by
    rw [← Category.assoc, ← pow_comp, ← comp_pow, hX, MonObj.comp_one, MonObj.one_comp]
  have h₂ : (fst T (G2 A) ≫ X ≫ snd A A) ^ k = 1 := by
    rw [← Category.assoc, ← pow_comp, ← comp_pow, hX, MonObj.comp_one, MonObj.one_comp]
  have z₁ : ∀ y, k • pc hP (fst T (G2 A) ≫ X ≫ fst A A) y = 0 := fun y => by
    rw [← pc_pow_left hP hB, h₁, pc_one_left hP hB]
  have z₂ : ∀ x, k • pc hP x (fst T (G2 A) ≫ X ≫ snd A A) = 0 := fun x => by
    rw [← pc_pow_right hP hB', h₂, pc_one_right hP hB']
  obtain ⟨t, ht⟩ : ∃ t : LB.Gen (Out.thetaLB (G2 A) P k X), t.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
    rw [cls_linComb hP, Fin.sum_univ_two]
    show (k : ℤ) • pull (snd T (G2 A)).left _ + (-(k : ℤ)) • pull (Out.translPt (G2 A) X).left _ = 0
    rw [e, e, tr, mul_comp, mul_comp, Category.assoc, Category.assoc, hB, hB', hB']
    simp only [natCast_zsmul, neg_smul, smul_add, z₁, z₂]
    abel
  exact ⟨⟨X, t, ht⟩, rfl⟩

end Theta

theorem exists_weilIs_prod_root : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    ∀ (k : ℕ), 0 < k → ∀ (T : Over S) (X Y : T ⟶ G2 A), X ^ k = 1 → Y ^ k = 1 →
    ∃ c : Γ(T.left, ⊤)ˣ, c ^ k = 1 ∧ Out.WeilIs (G2 A) P k X Y c := by
  intro S A _ _ hA P hP rig₁ rig₂ hamp k hk T X Y hX hY
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP rig₁ rig₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP rig₁ rig₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ Z : T ⟶ G2 A, Z ^ k = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp (G2 A) P k (Out.overRes V), θ.pt = Out.overResι V ≫ Z := fun Z hZ p => by
    obtain ⟨θ, hθ⟩ := exists_theta_prod hP hB hB' (k := k) (Out.overResι ⊤ ≫ Z)
      (by rw [← MonObj.comp_pow, hZ, MonObj.comp_one])
    exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG hAA hP (lifts X hX) (lifts Y hY)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG hAA hP (lifts 1 (one_pow k)) (lifts Y hY)
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ * c₁ = c₁ := CommutatorPairing.weilIs_unique hG hAA hP h11 hc₁
  have e₁' : c₁ = 1 := mul_eq_left.1 e₁
  have pw : ∀ m : ℕ, Out.WeilIs (G2 A) P k (X ^ (m + 1)) Y (c₀ ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hc₀
    | succ m ih =>
      rw [pow_succ X (m + 1), pow_succ c₀ (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP ih hc₀
  have hp := pw (k - 1)
  rw [Nat.sub_add_cancel hk, hX] at hp
  exact ⟨c₀, CommutatorPairing.weilIs_unique hG hAA hP hp (e₁' ▸ hc₁), hc₀⟩

end GlobalTheory.ProdPairing
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def Obj.toSieg {b : Base D R} {N : ℕ} {t : S ⟶ Sp R} (o : Obj b N t) {h M : ℕ} {B : Type} [CommRing B] {ζ : B}
    {t₁ : S ⟶ Sp B} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)} (hl : IsSympLev o.P h M ζ t₁ lev) :
    SiegPre h M ζ t₁ where
  A := o.A
  ab := o.ab
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  lev := lev
  lev_add := hl.1
  lev_tors := hl.2.1
  geom := hl.2.2

theorem Obj.toSieg_ample {b : Base D R} {N : ℕ} {t : S ⟶ Sp R} (o : Obj b N t) {h M : ℕ} {B : Type} [CommRing B]
    {ζ : B} {t₁ : S ⟶ Sp B} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)} (hl : IsSympLev o.P h M ζ t₁ lev) :
    Out.RelAmple (o.toSieg hl).A (o.toSieg hl).diag := o.ample

end GlobalTheory.UPel.HT
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum


theorem _root_.GlobalTheory.T.isTwistedThetaValue_unique : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A) (v v' : Γ(T.left, ⊤)), Odd N → IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ β x h v' → v = v' := by
  first | exact @GlobalTheory.UPoinc.USum.isTwVal_unique | exact GlobalTheory.UPoinc.USum.isTwVal_unique | (intros; apply GlobalTheory.UPoinc.USum.isTwVal_unique <;> assumption)
end
