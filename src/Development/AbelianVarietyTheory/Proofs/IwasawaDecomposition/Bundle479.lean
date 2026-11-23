module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle460
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle312
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle326
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle340
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle392
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle381
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle465
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFixedVectorOfTypeOccurringInRows
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle467
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle449
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle136
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle462
public import Formalism.LocalToGlobal.Columns.TwQLev
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle468
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle469
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.TrueRecord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {θ : InfF D}

abbrev cuspIn (θ : InfF D) (V : HSp D) : Submodule ℂ (AFs θ V) := (CuspS θ V).comap (AFs θ V).subtype

def cuspEq (θ : InfF D) (V : HSp D) : cuspIn θ V ≃ₗ[ℂ] CuspS θ V := Submodule.comapSubtypeEquivOfLe (CuspS_le θ V)

theorem mem_cuspIn (hθ : IsInfFam θ) {V : HSp D} (F : AFs θ V) : F ∈ cuspIn θ V ↔ IsCuspFun V F.1 :=
  (mem_CuspS (formSub D) hθ).trans ⟨fun h => h.2, fun h => ⟨aut hθ F, h⟩⟩

def trE (hθ : IsInfFam θ) (V : HSp D) (k : GA D V) (hk : ∀ φ, IsAutFunSm θ V φ → IsAutFunSm θ V (rTr V k φ)) :
    Module.End ℂ (AFs θ V) :=
  (LinearMap.funLeft ℂ ℂ fun g => g * k).restrict fun φ hφ => Submodule.subset_span (hk φ (aut hθ ⟨φ, hφ⟩))

theorem trE_cusp (hθ : IsInfFam θ) (V : HSp D) (k hk) (F : AFs θ V) (hF : F ∈ cuspIn θ V) : trE hθ V k hk F ∈ cuspIn θ V := by
  rw [mem_cuspIn hθ] at hF ⊢
  exact (GlobalTheory.T.isCuspFunction_closed_under_operations D V _ _ (aut hθ F).toIsAutFun (aut hθ F).toIsAutFun hF hF).2.2.1 k

def actFin (hθ : IsInfFam θ) (V : HSp D) : GfC V →* Module.End ℂ (AFs θ V) where
  toFun k := trE hθ V k fun φ h => GlobalTheory.T.smoothAutomorphicForm_rightTranslate_finiteAdelic D θ hθ V φ h k k.2
  map_one' := LinearMap.ext fun φ => Subtype.ext (funext fun g => congrArg φ.1 (mul_one g))
  map_mul' a b := LinearMap.ext fun φ => Subtype.ext (funext fun g => congrArg φ.1 (mul_assoc g a b).symm)


open Classical in
def actReal (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Module.End ℂ (AFs θ V) :=
  if h : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) then trE hθ V (atTau θ V τ g) fun φ hφ => GlobalTheory.T.isSmoothAutomorphicFunction_translate_atRealPlace D θ hθ V φ hφ τ g h else 1

theorem actReal_apply (hθ : IsInfFam θ) (V : HSp D) (τ) {g} (h : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (F : AFs θ V) (x) :
    (actReal hθ V τ g F).1 x = F.1 (x * atTau θ V τ g) := by
  rw [actReal, dif_pos h]; rfl

theorem mul_mem_UH {n : ℕ} {H g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH H) (hh : h ∈ Formalism.QuantumDeterminants.UH H) :
    g * h ∈ Formalism.QuantumDeterminants.UH H := by
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at *
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h := by simp only [Matrix.mul_assoc]
    _ = H := by rw [hg, hh]

def chrGrp (D : D7) : Subgroup (IdC D) := (GlobalTheory.T.heckeCharacter_infinityExponent_group_laws D).1.choose

theorem mem_chrGrp {χ : IdC D} : χ ∈ chrGrp D ↔ IsHC D χ := (GlobalTheory.T.heckeCharacter_infinityExponent_group_laws D).1.choose_spec χ

def expo (χ : chrGrp D) (τ : D.what₂.Tau) : ℚ := ((mem_chrGrp.1 χ.2).2 τ).choose

theorem expo_spec (χ : chrGrp D) (τ : D.what₂.Tau) : HasInfExp D χ.1 τ (expo χ τ) := ((mem_chrGrp.1 χ.2).2 τ).choose_spec

theorem expo_eq {χ : chrGrp D} {τ : D.what₂.Tau} {a : ℚ} (h : HasInfExp D χ.1 τ a) : expo χ τ = a :=
  (GlobalTheory.T.heckeCharacter_infinityExponent_group_laws D).2.1 _ _ _ _ (expo_spec χ τ) h

def ksph (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Subgroup (GfC V) :=
  (GlobalTheory.T.exists_lattice_stabiliser_subgroup_outside_places D V S).choose.subgroupOf (GfC V)

theorem mem_ksph {V : HSp D} {S} {g : GfC V} : g ∈ ksph V S ↔ (g : GA D V) ∈ KsphC V S := by
  rw [← (GlobalTheory.T.exists_lattice_stabiliser_subgroup_outside_places D V S).choose_spec.1]; rfl


open Classical in
def transp {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (Φ : ThS ψ V W) : ThS ψ W V :=
  if h : IsThetaFun ψ W V (fun x => Φ.1 x.transpose) then ⟨_, mem_ThS.2 h⟩ else 0

theorem transp_apply {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D} (h : V.rank ≠ W.rank)
    (Φ : ThS ψ V W) (x : WA V W) : (transp Φ).1 x.transpose = Φ.1 x := by
  rw [transp, dif_pos ((GlobalTheory.Mem.ThetaClosed.thetaFun_closed D ψ hψ V W Φ.1).2.2 h (mem_ThS.1 Φ.2))]
  rfl

abbrev Trip (D : D7) := Σ (A B : HSp D), A.V →ₗ[D.host.E] B.V

abbrev trip0 (D : D7) : Trip D := ⟨D.sp.X 0, D.sp.Y 0, D.sp.iXY 0⟩

def Bes1 (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Type := {d : BesDat A B ι // (d.y : GA D B) = 1}

def Is0 (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Prop := (⟨A, B, ι⟩ : Trip D) = trip0 D

def PosT (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Type :=
  (Odd (B.rank - A.rank) → Bes1 A B ι) ⊕ (D.what₂.Word × PLift (Is0 A B ι))

abbrev Ses (θ : InfF D) (A B : HSp D) : Type := AFs θ A →ₗ⋆[ℂ] CuspS θ B →ₗ[ℂ] ℂ

def bes0 (u : D.what₂.Word) : Bes1 (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) := ⟨memberBes D u, rfl⟩

def datT (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (ho : Odd (B.rank - A.rank)) : PosT A B ι → Bes1 A B ι
  | .inl f => f ho
  | .inr x => cast (congrArg (fun t : Trip D => Bes1 t.1 t.2.1 t.2.2) x.2.down.symm) (bes0 x.1)

theorem inr_eq (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (x : D.what₂.Word × PLift (Is0 A B ι)) :
    (⟨A, B, ι, .inr x⟩ : Σ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V), PosT A A' ι) =
      ⟨D.sp.X 0, D.sp.Y 0, D.sp.iXY 0, .inr (x.1, ⟨rfl⟩)⟩ := by
  obtain ⟨u, ⟨h⟩⟩ := x
  cases h
  rfl

theorem inr_ne (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (x : D.what₂.Word × PLift (Is0 A B ι)) (f) :
    ¬ HEq (.inr x : PosT A B ι) (.inl f : PosT (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0)) := by
  obtain ⟨u, ⟨h⟩⟩ := x
  cases h
  intro h
  cases eq_of_heq h

section Scale

variable {P Q R : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] [AddCommGroup R] [Module ℂ R]
  (a : ℂ) (b : P →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ) (e : R ≃ₗ[ℂ] Q)

theorem ses_add (x x' : P) (y : Q) : a * b (x + x') y = a * b x y + a * b x' y := by simp [mul_add]

theorem ses_smul (c : ℂ) (x : P) (y : Q) : a * b (c • x) y = star c * (a * b x y) := by simp [mul_left_comm]

theorem ses_right (x : P) : IsLinearMap ℂ fun y : R => a * b x (e y) :=
  ⟨fun G G' => by simp [mul_add], fun c G => by simp [mul_left_comm]⟩

end Scale

section Record

variable (hP : PetInt D) (hT : TopInt D) (hB : BesInt D) (hL : LiftAut D) (hθ : IsInfFam θ)
  {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (Wf : WeilFun D ψ) (Tw : Tow D) (Rc : RecFun D θ ψ)

def per1 (u : D.what₂.Word) : Ses θ (D.sp.X 0) (D.sp.Y 0) :=
  ((GlobalTheory.T.definiteBesselPeriod_sesquilinear D).2.2 θ hθ ψ hψ _ _ _ (Rc.per1.dat u) (D.sp.X_sig 0) (D.sp.X_def 0 (Nat.zero_le _))).choose


open Classical in
def perT (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : PosT A B ι → Ses θ A B
  | .inl f => if ho : Odd (B.rank - A.rank) then (exists_bes hB hθ hψ (f ho).1).choose else 0
  | .inr x => cast (congrArg (fun t : Trip D => Ses θ t.1 t.2.1) x.2.down.symm) (per1 hθ hψ Rc x.1)

theorem perT_inl {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (ho : Odd (B.rank - A.rank))
    (f : Odd (B.rank - A.rank) → Bes1 A B ι) :
    perT hB hθ hψ Rc A B ι (.inl f) = (exists_bes hB hθ hψ (f ho).1).choose := dif_pos ho

theorem perT_inr (u : D.what₂.Word) :
    perT hB hθ hψ Rc (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) (.inr (u, ⟨rfl⟩)) = per1 hθ hψ Rc u := rfl

theorem clause_inl {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (ho : Odd (B.rank - A.rank)) (hA : A.SigOK)
    (hι : HSpace.IsIsomEmb A B ι) (f : Odd (B.rank - A.rank) → Bes1 A B ι) {μ 𝓕} (hμ : IsVolPair D A μ 𝓕)
    {s : GA D A → GA D B} (hs : ∀ h, EmbRel B A ι (s h) h) (φ : AFs θ A) (F : cuspIn θ B) (hφ : IsAniso A ∨ φ ∈ cuspIn θ A) :
    GlobalTheory.BesselCompare.ClauseFlag ψ (f ho).1 μ 𝓕 s φ.1 F.1.1 (Rc.petC A)
      ((Rc.petC A : ℂ) * perT hB hθ hψ Rc A B ι (.inl f) φ (cuspEq θ B F)) := by
  intro ν 𝓝 h1 h2 h3
  have h := (exists_bes hB hθ hψ (f ho).1).choose_spec hA hι μ 𝓕 hμ s hs φ (cuspEq θ B F) hφ ν 𝓝 h1 h2 h3
  rw [perT_inl hB hθ hψ Rc ho f, h, one_mul]
  rfl

theorem memberPeriodAtTrivialPosition_spec (u : D.what₂.Word) {μ 𝓕} (hμ : IsVolPair D (D.sp.X 0) μ 𝓕) {ν 𝓝} (hν : (Rc.per1.dat u).bes.IsUnitPair ν 𝓝)
    {s : GA D (D.sp.X 0) → GA D (D.sp.Y 0)} (hs : ∀ h, EmbRel (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (s h) h)
    (φ : AFs θ (D.sp.X 0)) (F : cuspIn θ (D.sp.Y 0)) :
    (Rc.petC (D.sp.X 0) : ℂ) * perT hB hθ hψ Rc (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) (.inr (u, ⟨rfl⟩)) φ (cuspEq θ _ F) =
      (Rc.petC (D.sp.X 0) : ℂ) * (Rc.per1.dat u).period ψ μ 𝓕 ν 𝓝 s (fun g => star (φ.1 g)) F.1.1 := by
  rw [perT_inr, per1, ← ((GlobalTheory.T.definiteBesselPeriod_sesquilinear D).2.2 θ hθ ψ hψ _ _ _ (Rc.per1.dat u) (D.sp.X_sig 0)
    (D.sp.X_def 0 (Nat.zero_le _))).choose_spec μ 𝓕 hμ ν 𝓝 hν s hs φ (cuspEq θ _ F)]
  rfl

theorem adm {V W : HSp D} (χ χ' : chrGrp D) (h : V.rank ≠ W.rank) (h1 : ResEta D χ.1 V.rank) (h2 : ResEta D χ'.1 W.rank) :
    admitted V W χ.1 χ'.1 := ⟨h, mem_chrGrp.1 χ.2, mem_chrGrp.1 χ'.2, h1, h2⟩

theorem range_ThS (V W : HSp D) : Set.range (ThS ψ V W).subtype = {f | IsThetaFun ψ V W f} :=
  Set.ext fun f => ⟨fun ⟨x, hx⟩ => hx ▸ mem_ThS.1 x.2, fun h => ⟨⟨f, mem_ThS.2 h⟩, rfl⟩⟩

end Record

end GlobalTheory.Mem.TrueRecord

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt.UpMove

section G

variable {D : D7} {u : D.what₂.Word}



theorem upCl_of_crd (A : AtTTied u) (P : ∀ i hi, LvTied u A i hi) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (c : (D.mem u).C.cls i) (y : Formalism.L2.Herm.Ld D u i c)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hoff : ∀ q : HeightOneSpectrum (𝓞 D.host.E), q.asIdeal ≠ A.Pv v → q.asIdeal ≠ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (A.Pv v) →
      Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c (prH A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (clsCrd D u i hi c))
    (h3 : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c (prH A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.Ld D u i hi c))
    (h4 : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.Ld D u i hi c ⊔
          Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (toLd i hi c y).1}))
    (h5 : ∀ (x : ↥(Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH A P i v c y))))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Formalism.L2.Forms.Ld D u i hi c),
        (D.fm u).fv i v _ ((P i hi).pr v _ x) = (D.fm u).fv i v c ((P i hi).pr v c ⟨_, hx⟩))
    (h6 : ∀ v', v' ≠ v → ∀ (z : ↥(Formalism.L2.Forms.Ld D u i hi c))
        (z' : ↥(Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH A P i v c y)))), z.1 = γ.1.1 *ᵥ z'.1 →
        (D.fm u).fv i v' _ ((P i hi).pr v' _ z') = (D.fm u).fv i v' c ((P i hi).pr v' c z)) :
    UpCl A P i v c y (gx i hi γ) := by

  let crdL := ((crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))
  have inj : Function.Injective crdL := (crdN D i hi).injective
  have eCls : ∀ c' : (D.mem u).C.cls i, (D.clsLat u i c').map crdL = clsCrd D u i hi c' := fun _ => rfl
  have eLd : ∀ c' : (D.mem u).C.cls i, (Formalism.L2.Herm.Ld D u i c').map crdL = Formalism.L2.Forms.Ld D u i hi c' := fun c' =>
    dual_co D.sp.cm (D.sp.X i) (rankN D i hi) (D.clsLat u i c')
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q hq hP hc
    haveI := hq.isPrime
    let q' : HeightOneSpectrum (𝓞 D.host.E) :=
      ⟨q, hq.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hq (RingOfIntegers.not_isField D.host.E)⟩
    apply Submodule.map_injective_of_injective inj
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap, eCls, eCls]
    exact hoff q' hP hc
  · apply Submodule.map_injective_of_injective inj
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap, eCls, eLd]
    exact h3
  · apply Submodule.map_injective_of_injective inj
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap, eLd, Submodule.map_sup, eLd, Submodule.map_span, Set.image_singleton]
    convert h4 using 4
    simp [crdL, toLd]
  · intro z hz
    rw [prH_eq A P hi v _ z, prH_eq A P hi v c ⟨_, hz⟩]
    have key : crdN D i hi (((D.mem u).A.T : D.host.E) • (gx i hi γ).1 (z : (D.sp.X i).V)) =
        (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ (toLd i hi _ z).1) := by
      rw [map_smul, crdN_gx]
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
      rfl
    have hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ (toLd i hi _ z).1) ∈ Formalism.L2.Forms.Ld D u i hi c :=
      key ▸ (mem_Ld i hi c _).1 hz
    have e : toLd i hi c ⟨_, hz⟩ = ⟨_, hx⟩ := Subtype.ext key
    rw [e]
    exact h5 _ hx
  · intro v' hv' z hz
    rw [prH_eq A P hi v' _ z, prH_eq A P hi v' c ⟨_, hz⟩]
    exact h6 v' hv' (toLd i hi c ⟨_, hz⟩) (toLd i hi _ z) (crdN_gx i hi γ _)

end G

section S

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}



theorem crd_up (T : FormsTiedSym D u Ch chOf) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (c : (D.mem u).C.cls i) (y : Formalism.L2.Herm.Ld D u i c)
    (hf : (D.fm u).fv i v c (prH T.atT T.lv i v c y) = 1)
    (hC : ∀ (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (c' : (D.mem u).C.cls i) (z : Formalism.L2.Forms.Ld D u i (le_of_succ_m h2) c')
      (z' : LdG D i (le_of_succ_m h2) (clsCrd D u i (le_of_succ_m h2) c')), z'.1 = z.1 →
        (T.lvC i h1 h2).pr v c' z' = (T.lv i (le_of_succ_m h2)).pr v c' z) :
    ∃ γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi),
      AdC T i hi c ((D.fm u).up i v c (prH T.atT T.lv i v c y)) γ.1 (T.atT.eV v).1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c (prH T.atT T.lv i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Formalism.L2.Forms.Ld D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH T.atT T.lv i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Formalism.L2.Forms.Ld D u i hi c ⊔
          Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (toLd i hi c y).1}) ∧
      ∀ (x : ↥(Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH T.atT T.lv i v c y))))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Formalism.L2.Forms.Ld D u i hi c),
        (D.fm u).fv i v _ ((T.lv i hi).pr v _ x) = (D.fm u).fv i v c ((T.lv i hi).pr v c ⟨_, hx⟩) := by
  have e1 : (T.lv i hi).pr v c (toLd i hi c y) = prH T.atT T.lv i v c y := (prH_eq T.atT T.lv hi v c y).symm
  rcases (show (i = 0 ∨ i = D.R.m) ∨ (1 ≤ i ∧ i + 1 ≤ D.R.m) by omega) with h | ⟨h1, h2⟩
  · have hz : (D.fm u).fv i v c ((T.lv i hi).pr v c (toLd i hi c y)) = 1 := by rw [e1]; exact hf
    have H0 := T.upN i hi h v c (toLd i hi c y) hz
    generalize (T.lv i hi).pr v c (toLd i hi c y) = t at H0 e1
    subst e1
    obtain ⟨γ, η, κ, hη, hy, h3, h4, h5, -⟩ := H0
    refine ⟨γ, ⟨fun h' => ⟨κ.1, κ.2, η.1, η.2, hη, hy⟩, fun h1 h2 => absurd h (by omega)⟩, h3, h4, h5⟩
  · have hl := le_of_succ_m h2
    have e0 : (T.lvC i h1 h2).pr v c (toLd i hi c y) = prH T.atT T.lv i v c y :=
      (hC h1 h2 c (toLd i hi c y) (toLd i hi c y) rfl).trans e1
    have hz : (D.fm u).fv i v c ((T.lvC i h1 h2).pr v c (toLd i hi c y)) = 1 := by rw [e0]; exact hf
    have H0 := T.upC i h1 h2 v (chOf i c) ⟨c, rfl⟩ (toLd i hi c y) hz
    generalize (T.lvC i h1 h2).pr v c (toLd i hi c y) = t at H0 e0
    subst e0
    obtain ⟨hβ, γ, η, κ, hη, hy, h3, h4, h5, -⟩ := H0
    refine ⟨γ, ⟨fun h => absurd h (by omega), fun h1' h2' => ⟨hβ, κ.1, κ.2, η.1, η.2, hη, hy⟩⟩, h3, h4, fun x hx => ?_⟩
    have := h5 x hx
    rwa [hC h1 h2 _ x x rfl, hC h1 h2 c ⟨_, hx⟩ ⟨_, hx⟩ rfl] at this

end S

end GlobalTheory.Mem.Col2.HAt.UpMove


open GlobalTheory.Mem.Col2.HAt.UpMove in

theorem GlobalTheory.Mem.Col2.HAt.UpMove.up_move : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (c : ((I.rec7 l Z).mem u).C.cls i) (y : Formalism.L2.Herm.Ld (I.rec7 l Z) u i c), ∃ γ, i ≤ (I.rec7 l Z).R.m → ((I.rec7 l Z).fm u).fv i v c (prH (F u).atT (F u).lv i v c y) = 1 → UpCl (F u).atT (F u).lv i v c y γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).up i v c (prH (F u).atT (F u).lv i v c y)) γ v := by
  intro B X I hOk hPins l Z H F hStd hCar u i v c y
  by_cases hi : i ≤ (I.rec7 l Z).R.m
  swap
  · exact ⟨1, fun h => absurd h hi⟩
  by_cases hf : ((I.rec7 l Z).fm u).fv i v c (prH (F u).atT (F u).lv i v c y) = 1
  swap
  · exact ⟨1, fun _ h => absurd h hf⟩
  obtain ⟨γ, hAd, h3, h4, h5⟩ := crd_up (F u) i hi v c y hf
    (fun h1 h2 c' z z' e => (GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hOk hPins l Z H F hStd hCar u i h1 h2 v c').1 z z' e)
  refine ⟨gx i hi γ, fun _ _ => ⟨upCl_of_crd (F u).atT (F u).lv i hi v c y γ ?_ h3 h4 h5 ?_,
    GlobalTheory.T.adelic_relation_classes_coordinates I hOk hPins l Z H F hStd hCar u i hi v c _ γ hAd⟩⟩
  · intro q hP hc
    refine GlobalTheory.T.adelic_conjugate_character_standard_forms I hOk hPins l Z H F hStd hCar u i hi v c _ γ.1 hAd q fun hq => ?_
    rcases GlobalTheory.T.host_primes_over_level_place I hOk hPins l Z H F hStd hCar u v q hq with h | h
    · exact hP h
    · exact hc h
  · intro v' hv' z z' e
    exact GlobalTheory.T.levelFunctional_eq_of_classes_related_at_place I hOk hPins l Z H F hStd hCar u i hi v v' c _ γ.1 hAd hv' z z' e
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.finiteTypeIsotypicPart_eq_iSup_equivariantHoms_frame : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π = ⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M), LinearMap.range f := by
  first | exact @GlobalTheory.IsotHom.isotIn_eq_iSup_homInto | exact GlobalTheory.IsotHom.isotIn_eq_iSup_homInto | (intros; apply GlobalTheory.IsotHom.isotIn_eq_iSup_homInto <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.isAdmissible_finiteType_frame_of_cuspMap : GlobalTheory.Published.HarishChandraFinite → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V V' : HSp D) {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel V' S') (Φ : GfC V ≃ₜ* GfC V') (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P' : LevelP L.Pg L.r ℂ) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), L.s = 0 → L.Q = ∅ → killed ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (eqSet V β L eG c P' (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) ≠ ⊥ → (homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M) ≠ ⊥ ∨ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) ((finRep M').comp Φ.toMulEquiv.toMonoidHom) (allMaps θ M') ≠ ⊥) → GlobalTheory.PRep.IsAdmissible ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) := by
  first | exact @GlobalTheory.AdmOfHom.isAdmissible_finRep | exact GlobalTheory.AdmOfHom.isAdmissible_finRep | (intros; apply GlobalTheory.AdmOfHom.isAdmissible_finRep <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.isotypicSum_eq_of_frames_innerConj : ∀ {D : D7} (Y W : HSp D) {n : ℕ} (PY : principalLevelFrame.RowPsi Y n) (PW : principalLevelFrame.RowPsi W n) (Φ : GfC Y ≃ₜ* GfC W) (h : Formalism.AUTREP.GAf D.host.E n), (∀ κ, ((Φ ⟨PY.ψ κ, PY.into κ⟩ : GfC W) : GA D W) = PW.ψ (h * κ * h⁻¹)) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC W) X) (C : Submodule ℂ X) (π : Formalism.L2.NG.FinTyp D.host.E n), (⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv PY).symm.toMonoidHom) (ρ.comp Φ.toMulEquiv.toMonoidHom) C, LinearMap.range f) = ⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv PW).symm.toMonoidHom) ρ C, LinearMap.range f := by
  first | exact @GlobalTheory.FrameIsot.iSup_homInto_frame_conj | exact GlobalTheory.FrameIsot.iSup_homInto_frame_conj | (intros; apply GlobalTheory.FrameIsot.iSup_homInto_frame_conj <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem GlobalTheory.SerCmp.eSerC_eq_eSerO : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (hζ : IsGenSys L.gen), t = L.teich → ∀ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t ht L.gen hζ), (∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC t ht L.gen hζ) τ (O.lab d τ)) → ∀ (r : ℕ) (f : (ZMod g)[X]), 1 ≤ r → GlobalTheory.GLq.eSerC L r f = eSerO O r f := by
  intro hG g _ L t ht hζ htL O hO r f hr
  have hcusp : ∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple V →
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L (O.lab d V) (fun x => V.character x) :=
    fun d V hd hs hc => GlobalTheory.T.isCuspidalCharacterOfPolynomial_of_cuspidalLabel g L t ht hζ htL d V _ hd ((GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hs).2 hc)
      (hO d V hd hs hc)
  have hB : ∀ τ : FDRep ℂ (GL (Fin r) (ZMod g)), CategoryTheory.Simple τ →
      (GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f ↔ Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f) := by
    intro τ hτ
    constructor
    · refine GlobalTheory.T.labelMap_label_of_classFunctionLabel g L O (fun d V P hd hs hc hP => ?_) (fun d χ hχ => ?_)
        (GlobalTheory.T.trace_harishChandra_induced_eq_product_characters g) (GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero g) (GlobalTheory.T.exists_blocks_of_cuspidal_character_list g) r τ f hτ
      · exact GlobalTheory.T.cuspidal_label_polynomial_unique_all_primes hG g L d P (O.lab d V) _ hP (hcusp d V hd hs hc)
      · obtain ⟨V, hV, hVχ⟩ := hχ.2.1
        have hχV : (fun x => V.character x) = χ := funext hVχ
        have hd : 1 ≤ d := hχ.1
        exact ⟨V, hV, (GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hV).1 (hχV ▸ hχ), hVχ⟩
    · exact GlobalTheory.T.classFunctionLabel_of_labelMap_label g L O hcusp (GlobalTheory.T.trace_harishChandra_induced_eq_product_characters g) (GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero g) r τ f hτ
  unfold GlobalTheory.GLq.eSerC Formalism.L2.NT.eSerO
  rw [GlobalTheory.T.finsum_centralIdempotentOfIrrCharacter_eq_simple]
  refine finsum_congr fun z => finsum_congr_Prop (propext ?_) fun _ => rfl
  constructor
  · rintro ⟨τ, hτ, hz, hl⟩
    exact ⟨τ, hτ, hz, (hB τ hτ).1 hl⟩
  · rintro ⟨τ, hτ, hz, hl⟩
    exact ⟨τ, hτ, hz, (hB τ hτ).2 hl⟩
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_conjugated_chartData_localLevel_at_Q : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) {π : 𝓞 E} {T f : ℕ} (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal) (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG) (hidx : (baseLb E n ST).toAddSubgroup.relIndex (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f)) (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG (E := E) (n := n) (SG := SG))) →* ℂˣ) {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (hO : QOpen q) (hQT : ∀ P : Q, (T : 𝓞 F) ∉ (qv F P.1).asIdeal) (σ₀ : K →+* ℂ) (b : GL (Fin n) (AfE F E)) (hbU : b ∈ UAd hc n) (hbV : ∀ v, bc (prV (E := E) v) b ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) (hbL : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, b.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) (hbT : ∀ v, v ∈ plUnder F ST → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)) (hbO : ∀ v, v ∉ badQ' (F := F) SG Q → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1) (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1) (bad : Set (HeightOneSpectrum (𝓞 F))) (hb : bad = badQ' (F := F) SG Q) {cl : Type} (stab : cl → Type) [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) (Fin n → E)) (s : cl → DecoF E n ST SG Q) (y : cl → GL (Fin n) (AfE F E)) (hy : ∀ c, y c ∈ UAd hc n) (hd : ∀ c, FrOver q (y c) (s c)) (hs : Function.Bijective fun c => (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ)) (hlat : ∀ c, lat c = (s c).deco.1.L) (st : ∀ c, stab c →* GL (Fin n) E) (hinj : ∀ c, Function.Injective (st c)) (hr : ∀ c γ, γ ∈ (st c).range ↔ ∃ g : UF E n × ↥(Subgroup.pi Set.univ Hw : Subgroup (GLG (E := E) (n := n) (SG := SG))) × ↥Θ.grp, ufGL E n g.1 = γ ∧ g • s c = s c) (hchr : ∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ k, q.chr P k ^ m = 1), ∃ (lev : StepLevel F E hc.sig J T f bad) (Y : cl → UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (SI : ∀ c, stab c →* UJ (hc.sig : E →+* E) J), Function.Bijective (fun c => (Quotient.mk'' (Y c) : Cls lev)) ∧ (∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F), x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔ ((Y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) lev.Lb) ∧ (∀ c, Function.Injective (SI c)) ∧ (∀ c (γ : UJ (hc.sig : E →+* E) J), γ ∈ (SI c).range ↔ bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ lev.U.map (MulAut.conj (Y c).1).toMonoidHom) ∧ lev.Lb = baseLb E n ST ∧ lev.U = (levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).map (MulAut.conj b).toMonoidHom ∧ (∀ (x : lev.U) (z : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q), x.1 = b * z.1 * b⁻¹ → lev.chi x = ((levTyp lam).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ₀)⁻¹ : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q →* ℂˣ) z) ∧ (∃ m : ℕ, 0 < m ∧ ∀ κ, lev.chi κ ^ m = 1) ∧ (∀ c, (Y c).1 = y c * b⁻¹) ∧ ∀ c a, (SI c a).1 = st c a := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.chartQ_exists | exact GlobalTheory.Mem.Col2.ChEx.chartQ_exists | (intros; apply GlobalTheory.Mem.Col2.ChEx.chartQ_exists <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_conj_idempotentSum_over_level : ∀ (D : D7) (N : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ (e' : AE D) (P' : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e' P' ∧ (∀ PP ∈ P', ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ cA D e' = e := by
  first | exact @GlobalTheory.HalfLevelConj.exists_conj_idemSum | exact GlobalTheory.HalfLevelConj.exists_conj_idemSum | (intros; apply GlobalTheory.HalfLevelConj.exists_conj_idemSum <;> assumption)
end
