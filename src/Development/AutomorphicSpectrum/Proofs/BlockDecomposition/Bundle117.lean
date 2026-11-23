module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle098
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.EtaleLift

theorem existsUnique_lift_of_nilpotent {P E C D : Type} [CommRing P] [CommRing E] [CommRing C] [CommRing D]
    (ψ : P →+* E) (hψ : ψ.Etale) (u : C →+* D) (hu : Function.Surjective u)
    (hn : IsNilpotent (RingHom.ker u)) (f : P →+* C) (g : E →+* D) (h : g.comp ψ = u.comp f) :
    ∃! l : E →+* C, l.comp ψ = f ∧ u.comp l = g := by
  letI : Algebra P E := ψ.toAlgebra
  letI : Algebra P C := f.toAlgebra
  letI : Algebra P D := (u.comp f).toAlgebra
  haveI : Algebra.Etale P E := hψ
  let uA : C →ₐ[P] D := { u with commutes' := fun _ => rfl }
  let gA : E →ₐ[P] D := { g with commutes' := fun r => congrArg (fun t : P →+* D => t r) h }
  have hn₁ : IsNilpotent (RingHom.ker (uA : C →+* D)) := hn
  have hn₂ : IsNilpotent (RingHom.ker uA) := hn
  let lA : E →ₐ[P] C := Algebra.FormallySmooth.liftOfSurjective gA uA hu hn₁
  have hl : ∀ x, u (lA x) = g x := fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply gA uA hu hn₂ x
  refine ⟨(lA : E →+* C), ⟨RingHom.ext fun r => lA.commutes r, RingHom.ext hl⟩, ?_⟩
  rintro l' ⟨h1, h2⟩
  let lA' : E →ₐ[P] C := { l' with commutes' := fun r => congrArg (fun t : P →+* C => t r) h1 }
  have : lA' = lA := Algebra.FormallyUnramified.ext' u hn lA' lA fun x => by
    rw [hl]; exact congrArg (fun t : E →+* D => t x) h2
  exact congrArg (fun t : E →ₐ[P] C => (t : E →+* C)) this

variable {B : Type} [CommRing B] (J : Ideal B)

abbrev toBase (n : ℕ) : B ⧸ J ^ (n + 1) →+* B ⧸ J :=
  Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero n))

theorem isNilpotent_ker_toBase (n : ℕ) : IsNilpotent (RingHom.ker (toBase J n)) := by
  refine ⟨n + 1, ?_⟩
  have hk : RingHom.ker (toBase J n) = J.map (Ideal.Quotient.mk (J ^ (n + 1))) := by
    rw [Ideal.Quotient.factor_ker]
  rw [hk, ← Ideal.map_pow]
  simp

theorem existsUnique_level {P E : Type} [CommRing P] [CommRing E] (ψ : P →+* E) (hψ : ψ.Etale)
    (f : P →+* B) (g : E →+* B ⧸ J) (h : g.comp ψ = (Ideal.Quotient.mk J).comp f) (n : ℕ) :
    ∃! l : E →+* B ⧸ J ^ (n + 1), l.comp ψ = (Ideal.Quotient.mk _).comp f ∧ (toBase J n).comp l = g :=
  existsUnique_lift_of_nilpotent ψ hψ (toBase J n) (Ideal.Quotient.factor_surjective _)
    (isNilpotent_ker_toBase J n) _ g h

theorem iInf_pow_eq_bot (hJ : IsAdicComplete J B) : ⨅ i : ℕ, J ^ i = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  refine (Ideal.mem_bot).2 (IsHausdorff.haus hJ.toIsHausdorff x fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact (Ideal.mem_iInf.1 hx) n

end GlobalTheory.CompanionTheory.EtaleLift


open GlobalTheory.CompanionTheory.EtaleLift in
theorem GlobalTheory.CompanionTheory.EtaleLift.etLift_of_isAdicComplete :
    ∀ {B : Type} [CommRing B] (J : Ideal B), IsAdicComplete J B → EtLift J := by
  intro B _ J hJ P E _ _ ψ hψ f g h
  haveI := hJ
  choose l hl hu using existsUnique_level J ψ hψ f g h
  have hcomp : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J (Nat.succ_le_succ hle)).comp (l n) = l m := by
    intro m n hle
    refine (hu m _ ⟨?_, ?_⟩).symm ▸ rfl
    · rw [RingHom.comp_assoc, (hl n).1]
      rfl
    · rw [← (hl n).2, ← RingHom.comp_assoc]
      congr 1
      exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  let F : (n : ℕ) → E →+* B ⧸ J ^ n := fun n => (Ideal.Quotient.factorPow J (Nat.le_succ n)).comp (l n)
  have hF : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp (F n) = F m := by
    intro m n hle
    simp only [F]
    rw [← hcomp hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
    congr 1
    exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  let H : E →+* B := IsAdicComplete.liftRingHom J F hF
  have hH : ∀ n x, Ideal.Quotient.mk (J ^ n) (H x) = F n x := fun n x =>
    IsAdicComplete.mk_liftRingHom J F hF n x
  have h1 : H.comp ψ = f := by
    ext p
    rw [← sub_eq_zero]
    refine IsHausdorff.haus hJ.toIsHausdorff _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, map_sub,
      RingHom.comp_apply, hH, sub_eq_zero]
    have := congrArg (fun t : P →+* B ⧸ J ^ (n + 1) => Ideal.Quotient.factorPow J (Nat.le_succ n) (t p)) (hl n).1
    exact this
  have h2 : (Ideal.Quotient.mk J).comp H = g := by
    ext x
    have e1 : (toBase J 0).comp (Ideal.Quotient.factorPow J (Nat.le_succ 1)) = toBase J 1 :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
    have e2 : Ideal.Quotient.mk J (H x) = toBase J 0 (F 1 x) := by
      rw [← hH 1 x]
      rfl
    rw [RingHom.comp_apply, e2, ← (hl 1).2, ← e1]
    rfl
  refine ⟨H, ⟨h1, h2⟩, ?_⟩
  rintro H' ⟨h1', h2'⟩
  letI : Algebra P E := ψ.toAlgebra
  letI : Algebra P B := f.toAlgebra
  haveI : Algebra.Etale P E := hψ
  let A : E →ₐ[P] B := { H with commutes' := fun r => congrArg (fun t : P →+* B => t r) h1 }
  let A' : E →ₐ[P] B := { H' with commutes' := fun r => congrArg (fun t : P →+* B => t r) h1' }
  have : A' = A := Algebra.FormallyUnramified.ext_of_iInf J (iInf_pow_eq_bot J hJ) fun x => by
    exact (congrArg (fun t : E →+* B ⧸ J => t x) h2').trans (congrArg (fun t : E →+* B ⧸ J => t x) h2).symm
  exact congrArg (fun t : E →ₐ[P] B => (t : E →+* B)) this
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.EtNil

theorem isNilpotent_of_fg_of_le {B : Type} [CommRing B] {J J' : Ideal B}
    (hJ : ∀ x ∈ J, IsNilpotent x) (hfg : J'.FG) (hle : J' ≤ J) : IsNilpotent J' :=
  (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 fun x hx => mem_nilradical.2 (hJ x (hle hx))

theorem exists_lift {P E B : Type} [CommRing P] [CommRing E] [CommRing B] [Algebra P E]
    [Algebra P B] [Algebra.FormallySmooth P E] [Algebra.FinitePresentation P E] (J : Ideal B)
    (hJ : ∀ x ∈ J, IsNilpotent x) (g : E →ₐ[P] B ⧸ J) :
    ∃ h : E →ₐ[P] B, (Ideal.Quotient.mkₐ P J).comp h = g := by
  obtain ⟨n, π, hπ, hK⟩ := Algebra.FinitePresentation.out (R := P) (A := E)
  choose b hb using fun i => Ideal.Quotient.mk_surjective (g (π (MvPolynomial.X i)))
  let φ : MvPolynomial (Fin n) P →ₐ[P] B := MvPolynomial.aeval b
  have hφ : (Ideal.Quotient.mkₐ P J).comp φ = g.comp π :=
    MvPolynomial.algHom_ext fun i => by simp [φ, hb]
  have hφ' : ∀ p, Ideal.Quotient.mk J (φ p) = g (π p) := fun p => DFunLike.congr_fun hφ p
  let J' : Ideal B := (RingHom.ker π.toRingHom).map φ.toRingHom
  have hle : J' ≤ J := by
    refine Ideal.map_le_iff_le_comap.2 fun p hp => ?_
    have hp0 : π p = 0 := hp
    refine Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.1 ?_)
    change Ideal.Quotient.mk J (φ p) = 0
    rw [hφ', hp0, map_zero]
  have hnil : IsNilpotent J' := isNilpotent_of_fg_of_le hJ (hK.map _) hle
  have hkill : ∀ a ∈ RingHom.ker π, ((Ideal.Quotient.mkₐ P J').comp φ) a = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem φ.toRingHom ha)
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  let g' : E →ₐ[P] B ⧸ J' :=
    (Ideal.Quotient.liftₐ (RingHom.ker π) ((Ideal.Quotient.mkₐ P J').comp φ) hkill).comp
      e.symm.toAlgHom
  have hg' : ∀ p, g' (π p) = Ideal.Quotient.mk J' (φ p) := fun p => by
    have : e.symm (π p) = Ideal.Quotient.mk (RingHom.ker π) p := by
      rw [AlgEquiv.symm_apply_eq]
      exact (Ideal.quotientKerAlgEquivOfSurjective_mk hπ p).symm
    change Ideal.Quotient.liftₐ (RingHom.ker π) ((Ideal.Quotient.mkₐ P J').comp φ) hkill
      (e.symm (π p)) = _
    rw [this]
    rfl
  refine ⟨Algebra.FormallySmooth.lift J' hnil g', AlgHom.ext fun x => ?_⟩
  obtain ⟨p, rfl⟩ := hπ x
  have h1 := Algebra.FormallySmooth.mk_lift J' hnil g' (π p)
  rw [hg', Ideal.Quotient.eq] at h1
  change Ideal.Quotient.mk J (Algebra.FormallySmooth.lift J' hnil g' (π p)) = g (π p)
  rw [← hφ', Ideal.Quotient.eq]
  exact hle h1

theorem lift_unique {P E B : Type} [CommRing P] [CommRing E] [CommRing B] [Algebra P E]
    [Algebra P B] [Algebra.FormallyUnramified P E] [Algebra.FinitePresentation P E] (J : Ideal B)
    (hJ : ∀ x ∈ J, IsNilpotent x) (h₁ h₂ : E →ₐ[P] B)
    (H : ∀ x, Ideal.Quotient.mk J (h₁ x) = Ideal.Quotient.mk J (h₂ x)) : h₁ = h₂ := by
  obtain ⟨n, π, hπ, -⟩ := Algebra.FinitePresentation.out (R := P) (A := E)
  let d : Fin n → B := fun i => h₁ (π (MvPolynomial.X i)) - h₂ (π (MvPolynomial.X i))
  let J' : Ideal B := Ideal.span (Set.range d)
  have hfg : J'.FG := Submodule.fg_span (Set.finite_range d)
  have hle : J' ≤ J := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact Ideal.Quotient.eq.1 (H _)
  have hnil : IsNilpotent J' := isNilpotent_of_fg_of_le hJ hfg hle
  have hc : (Ideal.Quotient.mkₐ P J').comp (h₁.comp π) =
      (Ideal.Quotient.mkₐ P J').comp (h₂.comp π) :=
    MvPolynomial.algHom_ext fun i =>
      Ideal.Quotient.eq.2 (Ideal.subset_span ⟨i, rfl⟩)
  refine Algebra.FormallyUnramified.ext J' hnil fun x => ?_
  obtain ⟨p, rfl⟩ := hπ x
  exact DFunLike.congr_fun hc p

end GlobalTheory.CompanionTheory.EtNil

theorem GlobalTheory.CompanionTheory.EtNil.etLift_of_nil : ∀ {B : Type} [CommRing B] (J : Ideal B),
    (∀ x ∈ J, IsNilpotent x) → EtLift J := by
  intro B _ J hJ P E _ _ ψ hψ f g hg
  letI := ψ.toAlgebra
  letI := f.toAlgebra
  haveI : Algebra.Etale P E := hψ
  let gA : E →ₐ[P] B ⧸ J :=
    { g with commutes' := fun p => DFunLike.congr_fun hg p }
  obtain ⟨h, hh⟩ := GlobalTheory.CompanionTheory.EtNil.exists_lift J hJ gA
  have hh' : ∀ x, Ideal.Quotient.mk J (h x) = g x := fun x => DFunLike.congr_fun hh x
  refine ⟨h.toRingHom, ⟨RingHom.ext fun p => h.commutes p, RingHom.ext hh'⟩, ?_⟩
  rintro h' ⟨h1, h2⟩
  let hA : E →ₐ[P] B := { h' with commutes' := fun p => DFunLike.congr_fun h1 p }
  have : hA = h := GlobalTheory.CompanionTheory.EtNil.lift_unique J hJ hA h fun x => by
    change Ideal.Quotient.mk J (h' x) = _
    rw [hh']
    exact DFunLike.congr_fun h2 x
  exact RingHom.ext fun x => DFunLike.congr_fun this x
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix

namespace GlobalTheory.CompanionTheory.MirFourier

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (n : ℕ) (N : ℤ) : Subgroup (Multiplicative (Fin n → k)) where
  carrier := {x | ∀ i, x.toAdd i ∈ valBall k N}
  mul_mem' := by
    intro a b ha hb i
    simpa using add_mem (ha i) (hb i)
  one_mem' := by
    intro i
    simp
  inv_mem' := by
    intro a ha i
    simpa using neg_mem (ha i)

theorem mem_box {n : ℕ} {N : ℤ} {x : Multiplicative (Fin n → k)} :
    x ∈ box k n N ↔ ∀ i, x.toAdd i ∈ valBall k N := Iff.rfl

theorem box_antitone (n : ℕ) {M N : ℤ} (h : M ≤ N) : box k n N ≤ box k n M :=
  fun _ hx i => valBall_antitone h (hx i)

def chi (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) : Multiplicative (Fin n → k) →* ℂˣ where
  toFun x := Circle.toUnits (ψ (a ⬝ᵥ x.toAdd))
  map_one' := by simp
  map_mul' x y := by simp [dotProduct_add, AddChar.map_add_eq_mul]

theorem chi_apply (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (x : Multiplicative (Fin n → k)) :
    chi k ψ a x = Circle.toUnits (ψ (a ⬝ᵥ x.toAdd)) := rfl

abbrev chiOn (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (H : Subgroup (Multiplicative (Fin n → k))) :
    H →* ℂˣ := (chi k ψ a).comp H.subtype

def unipMir (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n :=
  (unip k n).codRestrict (Mir k n) (fun x => MirU_le_Mir k n ⟨x, rfl⟩)

@[simp] theorem coe_unipMir (n : ℕ) (x : Multiplicative (Fin n → k)) :
    ((unipMir k n x : Mir k n) : GL (Fin (n + 1)) k) = unip k n x := rfl

variable {k}

theorem exists_unipMir {n : ℕ} (u : MirUin k n) : ∃ x, unipMir k n x = (u : Mir k n) := by
  obtain ⟨x, hx⟩ := (Subgroup.mem_subgroupOf.1 u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  exact ⟨x, Subtype.ext hx⟩

theorem mem_chi_zero {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle)
    (τ : Representation ℂ (Mir k (m + 1)) V) {w : V} (hw : w ∈ twKer τ (MirUin k (m + 1)) 1) :
    w ∈ twKer (τ.comp (unipMir k (m + 1))) ⊤ (chiOn k ψ 0 ⊤) := by
  refine (Submodule.span_le.2 ?_) hw
  rintro _ ⟨u, w, rfl⟩
  obtain ⟨x, hx⟩ := exists_unipMir u
  refine Submodule.subset_span ⟨⟨x, trivial⟩, w, ?_⟩
  simp [chi_apply, hx]

theorem mem_chi_row {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle)
    (τ : Representation ℂ (Mir k (m + 1)) V) (g : GL (Fin (m + 1)) k) {w : V}
    (hw : w ∈ twKer τ (MirUin k (m + 1)) (mirChar k ψ m)) :
    τ (levi k (m + 1) g⁻¹) w ∈ twKer (τ.comp (unipMir k (m + 1))) ⊤
      (chiOn k ψ (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) ⊤) := by
  have hle : twKer τ (MirUin k (m + 1)) (mirChar k ψ m) ≤
      (twKer (τ.comp (unipMir k (m + 1))) ⊤
        (chiOn k ψ (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) ⊤)).comap
        (τ (levi k (m + 1) g⁻¹)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, w, rfl⟩
    obtain ⟨x, hx⟩ := exists_unipMir u
    set y : Multiplicative (Fin (m + 1) → k) :=
      Multiplicative.ofAdd (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec x.toAdd)
      with hy
    have hconj : levi k (m + 1) g⁻¹ * (u : Mir k (m + 1)) = unipMir k (m + 1) y * levi k (m + 1) g⁻¹ := by
      apply Subtype.ext
      show glEmb k (m + 1) g⁻¹ * ((u : Mir k (m + 1)) : GL (Fin (m + 2)) k) = unip k (m + 1) y * glEmb k (m + 1) g⁻¹
      rw [← hx, coe_unipMir, glEmb_mul_unip']
    have hchar : mirChar k ψ m u = chi k ψ (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) y := by
      rw [mirChar_eq k ψ m u x (by rw [← hx]; rfl), chi_apply]
      congr 2
      have : (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) ⬝ᵥ y.toAdd =
          ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec y.toAdd) (Fin.last m) := rfl
      rw [this, hy, toAdd_ofAdd, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul, ← Module.End.mul_apply, ← map_mul, hconj, map_mul,
      Module.End.mul_apply, hchar]
    exact Submodule.subset_span ⟨⟨y, trivial⟩, τ (levi k (m + 1) g⁻¹) w, rfl⟩
  exact hle hw

end GlobalTheory.CompanionTheory.MirFourier

end
end

section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem isDom_monoid : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), D.IsDom 1 ∧ ∀ t t' : D.T, D.IsDom t → D.IsDom t' → D.IsDom (t * t') := by
  intro G _ _ _ D
  refine ⟨⟨fun n hn => by simpa using hn, fun n hn => by simpa using hn,
    fun x hx => ⟨by simpa using hx, by simpa using hx⟩⟩, ?_⟩
  rintro t t' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
  refine ⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ⟨?_, ?_⟩⟩
  · have h := h1 _ (h1' n hn)
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := h2' _ (h2 n hn)
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := (h3 _ (h3' x hx).1).1
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := (h3' _ (h3 x hx).2).2
    rw [Subgroup.coe_mul]
    convert h using 1
    group

end GlobalTheory.CompanionTheory.Cass
end

section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem proj_mem_fixed_piN (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (v : fixed π D.J) : D.proj π (v : V) ∈ fixed (D.piN π) D.JT := by
  intro t
  have ht : ((t : D.T) : G) ∈ D.J := Subgroup.mem_comap.mp t.2
  have hv : π ((t : D.T) : G) (v : V) = (v : V) := by
    have h := v.2 ⟨((t : D.T) : G), ht⟩
    simpa using h
  have hq : (D.piN π) (t : D.T) (D.proj π (v : V)) = D.proj π (π ((t : D.T) : G) (v : V)) := rfl
  rw [hq, hv, MonoidHom.one_apply, Units.val_one, one_smul]

end GlobalTheory.CompanionTheory.Cass
end

section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeFix

theorem hk_mem_fixed : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V), ∀ v ∈ fixed ρ K, hk ρ K e v ∈ fixed ρ K ∧ ∀ g : GL ι F, (∀ q : GL ι F ⧸ K, e (g * q.out) = e q.out) → True := by
  intro F _ _ _ _ ι _ _ K e hE V _ _ ρ v hv
  refine ⟨?_, fun _ _ => trivial⟩
  have hfix : ∀ c ∈ K, ρ c v = v := by
    intro c hc
    have := hv ⟨c, hc⟩
    simpa using this
  have hbi := hE.2.2.2
  intro h
  have hk' : (h : GL ι F) ∈ K := h.2
  set k : GL ι F := (h : GL ι F) with hkdef
  have hinj : Function.Injective (ρ k : V →ₗ[ℂ] V) := by
    intro x y hxy
    have h1 : ∀ z, ρ k⁻¹ (ρ k z) = z := by
      intro z
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1 x, ← h1 y, hxy]
  have hstep : ∀ q : GL ι F ⧸ K, ρ k (e q.out • ρ q.out v) =
      e (k • q).out • ρ (k • q).out v := by
    intro q
    have hq : k • q = QuotientGroup.mk (k * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (k * q.out)
    rw [hq, hc, hbi k hk' c c.2 q.out, map_smul, map_mul, Module.End.mul_apply, map_mul,
      Module.End.mul_apply, hfix c c.2]
  have hsum : ρ k (hk ρ K e v) = hk ρ K e v := by
    unfold hk
    have h1 := AddMonoidHom.map_finsum_of_injective (ρ k : V →ₗ[ℂ] V).toAddMonoidHom hinj
      (fun q : GL ι F ⧸ K => e q.out • ρ q.out v)
    simp only [LinearMap.toAddMonoidHom_coe] at h1
    rw [h1]
    simp only [hstep]
    exact finsum_comp_equiv (f := fun q : GL ι F ⧸ K => e q.out • ρ q.out v) (MulAction.toPerm k)
  simpa using hsum

end GlobalTheory.CompanionTheory.HeckeFix
end

section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeSub

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem finite_cosets {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) :
    {q : GL ι F ⧸ K | e q.out ≠ 0}.Finite := by
  have hc : IsCompact (tsupport e) := hE.2.2.1
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun g : GL ι F => (fun x => g⁻¹ * x) ⁻¹' (K : Set (GL ι F)))
    (fun g => hE.1.preimage (continuous_const.mul continuous_id))
    (fun g _ => Set.mem_iUnion.2 ⟨g, by simp [K.one_mem]⟩)
  refine (t.finite_toSet.image (fun g => (QuotientGroup.mk g : GL ι F ⧸ K))).subset fun q hq => ?_
  have hq' : q.out ∈ tsupport e := subset_tsupport _ hq
  obtain ⟨g, hg, hgq⟩ := Set.mem_iUnion₂.1 (ht hq')
  exact ⟨g, hg, (QuotientGroup.eq.2 hgq).trans (QuotientGroup.out_eq' q)⟩

theorem hk_map {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL ι F) V) (σ : Representation ℂ (GL ι F) W) (f : V →ₗ[ℂ] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) (v : V) :
    f (hk ρ K e v) = hk σ K e (f v) := by
  unfold hk
  have hfin : (Function.support fun q : GL ι F ⧸ K => e q.out • ρ q.out v).Finite :=
    (finite_cosets hE).subset fun q hq h0 => hq (by simp [show e q.out = 0 from h0])
  rw [map_finsum f hfin]
  simp only [map_smul, hf]

end GlobalTheory.CompanionTheory.HeckeSub
end

section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.partial_fraction_off_diagonal_identity : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → ∀ i k, i ≠ k → 1 - ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.pfOrth | exact GlobalTheory.CompanionTheory.RgHeFrame.pfOrth | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.pfOrth <;> assumption)
end
