module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1375
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle227
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle294
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilVacuumFiniteSelfDualLatticeSplitting
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle080
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle253
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle342
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.MovesEntries

theorem map_mulVec_single {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (y : Fin n → A) (r s : Fin n) (h1 : f (y s) = 1)
    (h0 : ∀ b, b ≠ s → y b = 0) : f ((M *ᵥ y) r) = f (M r s) := by

  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [Finset.sum_eq_single s]
  · rw [h1, mul_one]
  · intro b _ hb
    rw [h0 b hb, map_zero, mul_zero]
  · intro hs
    exact (hs (Finset.mem_univ _)).elim

theorem toEAf_pair (D : D7) (α : Af D.host.F) (e : D.host.E) :
    toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] e) = e ⊗ₜ[D.host.F] α := by
  rfl

theorem infPart_pair (D : D7) (α : Af D.host.F) (e : D.host.E) :
    infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] e) = 0 := by
  have : infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] e)
      = (0 : Ainf D.host.F) ⊗ₜ[D.host.F] e := rfl
  rw [this, TensorProduct.zero_tmul]

theorem coord_int (D : D7) (S : HSp D) (L : GlobalTheory.FinPl.Lat S)
    (hL : ∀ z, z ∈ L ↔ z ∈ GlobalTheory.AdForm.intVec D S.rank) (v : HeightOneSpectrum (𝓞 D.host.F))
    (y : Fin S.rank → AE D) (hy : y ∈ GlobalTheory.FinPl.latV S L (fun _ => True)) (i : Fin S.rank) :
    Formalism.UG.prV (E := D.host.E) v (toEAf D (y i)) ∈ Formalism.BasicNotions.intV D.host.E v := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at ha
    subst ha
    have hxi : IsIntegral ℤ (x i) := (hL x).1 hx i
    have h1 : Formalism.UG.prV (E := D.host.E) v
        (toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)))
        = ((x i) ⊗ₜ[D.host.F] (1 : v.adicCompletion D.host.F))
          * ((1 : D.host.E) ⊗ₜ[D.host.F] (evalV D.host.F v α : v.adicCompletion D.host.F)) := by
      rw [toEAf_pair, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul]
      rfl
    show Formalism.UG.prV (E := D.host.E) v
        (toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i))) ∈ _
    rw [h1]
    refine Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨x i, ⟨⟨x i, hxi⟩, rfl⟩⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨evalV D.host.F v α, hα v⟩, rfl⟩))
  | zero =>
    rw [Pi.zero_apply, (toEAf D).map_zero, (Formalism.UG.prV (E := D.host.E) v).map_zero]
    exact Subring.zero_mem _
  | add a b _ _ ha hb =>
    rw [Pi.add_apply, (toEAf D).map_add, (Formalism.UG.prV (E := D.host.E) v).map_add]
    exact Subring.add_mem _ ha hb
  | neg a _ ha =>
    rw [Pi.neg_apply, (toEAf D).map_neg, (Formalism.UG.prV (E := D.host.E) v).map_neg]
    exact Subring.neg_mem _ ha

theorem finM_entry_int : ∀ (D : D7) (S : HSp D) {n : ℕ} (hn : S.rank = n) (L : GlobalTheory.FinPl.Lat S), (∀ z, z ∈ L ↔ z ∈ GlobalTheory.AdForm.intVec D S.rank) → ∀ κ : GA D S, GlobalTheory.FinPl.Moves S κ L L (fun _ => True) → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (r s : Fin n), Formalism.UG.prV (E := D.host.E) v (GlobalTheory.AdForm.finM S hn κ r s) ∈ Formalism.BasicNotions.intV D.host.E v := by
  intro D S n hn L hL κ hκ v r s
  subst hn
  let x : Fin S.rank → D.host.E := Pi.single s 1
  have hx : x ∈ L := by
    rw [hL]
    intro k
    by_cases hk : k = s
    · subst hk
      simp only [x, Pi.single_eq_same]
      exact isIntegral_one
    · simp only [x, Pi.single_eq_of_ne hk]
      exact isIntegral_zero
  let y : Fin S.rank → AE D := fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 * x i)
  have hy : y ∈ GlobalTheory.FinPl.latV S L (fun _ => True) := by
    refine AddSubgroup.subset_closure ⟨1, ?_, fun w hw => (hw trivial).elim, 1, rfl, x, hx, rfl⟩
    intro w
    rw [map_one]
    exact one_mem _
  have hid : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D (fun _ => True) := by
    intro i
    refine Submodule.mem_inf.2 ⟨infPart_pair D _ _, ?_⟩
    rw [Submodule.mem_iInf]
    intro w
    exact (w.2 trivial).elim
  have h := coord_int D S L hL v _ ((hκ y hid).1 hy) r
  have h2 : toEAf D ((Formalism.L2.Theta.mt S κ *ᵥ y) r) = toEAf D (Formalism.L2.Theta.mt S κ r s) := by
    refine map_mulVec_single (toEAf D) _ y r s ?_ ?_
    · simp only [y, x, toEAf_pair, Pi.single_eq_same, one_mul]
      rfl
    · intro b hb
      simp only [y, x, Pi.single_eq_of_ne hb, mul_zero, TensorProduct.tmul_zero]
  rw [h2] at h
  exact h

end GlobalTheory.FinPl.MovesEntries
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.StabMove

variable {D : D7}

def IntG (V : HSp D) (g : GA D V) : Prop := ∀ i j, finPart D (Formalism.L2.Theta.mt V g i j) ∈ intAE D

theorem IntG.inv {V : HSp D} (hV : V.gram = 1) {g : GA D V} (h : IntG V g) : IntG V g⁻¹ := by
  have e : ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D) := g.2
  rw [hV, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at e
  have e2 : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    rw [← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one]
  have e3 : Formalism.L2.Theta.mt V g⁻¹ = ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ := by
    rw [← Matrix.one_mul (Formalism.L2.Theta.mt V g⁻¹), ← e, Matrix.mul_assoc, e2, Matrix.mul_one]
  intro i j
  rw [e3, Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.MovedIdem.finPart_cA]
  exact GlobalTheory.MovedIdem.sigR_mem_intAE (h j i)

theorem intG_of_moves {V : HSp D} {n : ℕ} (hn : V.rank = n) {k : GA D V}
    (h : GlobalTheory.AdForm.Moves V hn k (Formalism.L2.Col.stdLat D.host.E n)) : IntG V k⁻¹ := by
  subst hn
  intro i j
  have h1 := (h (Pi.single j 1)).1 (fun a _ => by
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.one_le.1 le_rfl
    · exact zero_mem _) i
  refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
  have e : (fun a => eToEAf D ((Pi.single j 1 : Fin V.rank → D.host.E) a)) = Pi.single j 1 := by
    funext a
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  rw [e, Matrix.mulVec_single_one] at h1
  exact h1

theorem mem_hatV_iff {n : ℕ} (u : Fin n → GlobalTheory.Ker.AfE D) :
    u ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E n) ↔ ∀ i, u i ∈ intAE D := by
  constructor
  · intro hu i
    induction hu using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨a, ha, ⟨x i, (GlobalTheory.SW.Base.mem_stdL x).1 hx i⟩, rfl⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro hu
    rw [← Finset.univ_sum_single u]
    refine sum_mem fun i _ => ?_
    have key : ∀ z ∈ intAE D, (Pi.single i z : Fin n → GlobalTheory.Ker.AfE D) ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E n) := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, x, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), (GlobalTheory.SW.Base.mem_stdL _).2 fun b => ?_, ?_⟩
        · rw [Pi.single_apply]
          split_ifs
          · exact x.2
          · exact isIntegral_zero
        · funext b
          rw [Pi.single_apply, Pi.single_apply]
          split_ifs
          · rfl
          · rw [TensorProduct.tmul_zero]
      | zero => rw [Pi.single_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
      | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy
    exact key _ (hu i)

theorem isMov_of_intG {V : HSp D} {k : GA D V} (h : IntG V k) (h' : IntG V k⁻¹) :
    GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt V k) (GlobalTheory.SW.stdL D.host.E V.rank) (GlobalTheory.SW.stdL D.host.E V.rank) := by
  have key : ∀ g, IntG V g → ∀ u ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E V.rank),
      GlobalTheory.Ker.fmt V g *ᵥ u ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E V.rank) := fun g hg u hu =>
    (mem_hatV_iff _).2 fun i => sum_mem (t := Finset.univ) fun j _ => GlobalTheory.GeoActCompare.TameConj.mul_mem_intAE (hg i j) ((mem_hatV_iff _).1 hu j)
  intro u
  refine ⟨fun hu => ⟨_, key _ h' u hu, ?_⟩, ?_⟩
  · rw [Matrix.mulVec_mulVec, GlobalTheory.Ker.fmt, GlobalTheory.Ker.fmt, ← Matrix.map_mul, ← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel,
      GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  · rintro ⟨u₀, h0, rfl⟩
    exact key _ h u₀ h0

theorem finM_mul (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) : finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  change (Formalism.L2.Theta.mt V (g * h)).map (toEAf D) = (Formalism.L2.Theta.mt V g).map (toEAf D) * (Formalism.L2.Theta.mt V h).map (toEAf D)
  rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.map_mul]

theorem moves_of_mul {V : HSp D} {n : ℕ} (hn : V.rank = n) {g k : GA D V} (h : IntG V k) (h' : IntG V k⁻¹) {N}
    (hN : GlobalTheory.AdForm.Moves V hn (g * k) N) : GlobalTheory.AdForm.Moves V hn g N := by
  have key : ∀ a, IntG V a → ∀ u : Fin n → EF D, (∀ i, u i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
      ∀ i, (finM V hn a *ᵥ u) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun a ha u hu i =>
    sum_mem (t := Finset.univ) fun j _ => mul_mem
      (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart (ha ((finCongr hn).symm i) ((finCongr hn).symm j))) (hu j)
  intro x
  rw [hN x]
  constructor
  · intro hx
    have := key k h _ hx
    rwa [Matrix.mulVec_mulVec, ← finM_mul, _root_.mul_inv_rev, mul_inv_cancel_left] at this
  · intro hx
    have := key _ h' _ hx
    rwa [Matrix.mulVec_mulVec, ← finM_mul, ← _root_.mul_inv_rev] at this

theorem root_eq {V : HSp D} {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (hn : Even n) {g : GA D V} {x x' : (AE D)ˣ}
    (hx : IsDetRoot V g x) (hx' : IsDetRoot V g x') : χ x' = χ x := by
  obtain ⟨a, rfl⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 g x x' hx hx'
  obtain ⟨⟨η, hη⟩, h2⟩ := h
  obtain ⟨m, rfl⟩ := hn
  rw [map_mul, h2 η hη a, pow_add, ← mul_pow, GlobalTheory.VolHeckeCompare.IsEta_mul_self hη, one_pow, mul_one]

theorem coe_stdL (n : ℕ) : (GlobalTheory.SW.stdL D.host.E n : Set (Fin n → D.host.E)) = intVec D n :=
  Set.ext fun x => GlobalTheory.SW.Base.mem_stdL x

theorem om_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {δ : ℂ} {sc : ℝ} (hP : StdPair θ S T δ sc ψ)
    {μ : (AE D)ˣ →* Circle} {om : Om S T} (hW : IsWeilDatumO ψ S T μ μ om)
    (hu : ∀ v ε, GlobalTheory.WeilParts.NonSplitAt D v ε → GlobalTheory.WeilParts.UnramAt ε μ) {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) f) {k : GA D S} {k' : GA D T}
    (hk : k ∈ GfC S) (hk' : k' ∈ GfC T) (a : IntG S k) (a' : IntG T k') :
    ∃ x y, IsDetRoot S k x ∧ IsDetRoot T k' y ∧ om (k, k') f = (((μ x)⁻¹ * μ y : Circle) : ℂ) • f := by
  have m := isMov_of_intG a (a.inv hP.gS)
  have m' := isMov_of_intG a' (a'.inv hP.gT)
  have sS := GlobalTheory.Ker.Base.selfDualC_stdL hP.gS
  have sT := GlobalTheory.Ker.Base.selfDualC_stdL hP.gT
  obtain ⟨x, hx, rx⟩ := GlobalTheory.LatticeUnitRoot.exists_finUnit_isDetRoot D S _ sS k hk m
  obtain ⟨y, hy, ry⟩ := GlobalTheory.LatticeUnitRoot.exists_finUnit_isDetRoot D T _ sT k' hk' m'
  have hc : ∀ V : HSp D, V.gram = 1 → ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun V hV τ => by
    have : gramAt D V τ = 1 := by
      unfold gramAt
      rw [hV]
      simp
    rw [this]
    exact GlobalTheory.AdTh.isCartanInv_one_splitStab _
  refine ⟨x, y, rx, ry, GlobalTheory.FinVac.om_vacuum_finite D S T ψ θ hP.inf hP.sigS hP.sigT μ μ om hW
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) (fun v ε hv => ⟨hu v ε hv, hu v ε hv⟩) (fun _ => 1) (fun _ => 1)
    (hc S hP.gS) (hc T hP.gT) _ _ sS sT f ?_ k hk k' hk' m m' x y hx hy rx ry⟩
  rwa [coe_stdL, coe_stdL]

end GlobalTheory.AdForm.StabMove
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MovedVac

theorem halfBack : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (e : AE D) (u : WO S T),
    IsHalf e (actO S T g h u) → IsHalf e u := by
  intro D S T g h e u hu
  have hA : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]
    exact congrArg Units.val (inv_mul_cancel (matHom T h))
  have hB : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]
    exact congrArg Units.val (inv_mul_cancel (matHom S g))
  have cancel : ∀ X : Matrix (Fin T.rank) (Fin S.rank) (AE D),
      HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h⁻¹) (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h) X)
        (Formalism.L2.Theta.mt S g⁻¹))) (Formalism.L2.Theta.mt S g) = X := by
    intro X
    simp only [Matrix.mul_assoc, hB, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
  have key : e • actO S T g h u = actO S T g h u := by
    ext i j; exact hu i j
  have key2 : e • u = u := by
    have h1 := congrArg (fun M : Matrix (Fin T.rank) (Fin S.rank) (AE D) =>
      HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h⁻¹) M) (Formalism.L2.Theta.mt S g)) key
    simp only [actO] at h1
    rw [cancel u] at h1
    simp only [Matrix.mul_smul, Matrix.smul_mul] at h1
    rw [cancel u] at h1
    exact h1
  intro i j
  have := congrFun (congrFun key2 i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this

theorem norm_weilRepresentation_thetaFunction_preserved : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : (AE D)ˣ →* Circle) (om : Om S T),
    IsWeilDatumO ψ S T μ μ om → ∀ f, IsThetaFunO ψ S T f → ∀ p (m : Measure (WO S T)) (𝓕 : Set (WO S T)),
    IsCovolOne (ratL T S) m 𝓕 → nrm2 m 𝓕 (om p f) = nrm2 m 𝓕 f := by
  intro D ψ S T μ om hW f hf p m 𝓕 hm
  have hU := hW.om_unit m 𝓕 hm.1 hm.2.1 p f hf
  have hf' := hW.om_pres p f hf
  haveI : OpensMeasurableSpace (WO S T) := ⟨le_rfl⟩
  have key : ∀ F : WO S T → ℂ, Continuous F → nrm2 m 𝓕 F = (∫⁻ w in 𝓕, ‖F w‖ₑ ^ 2 ∂m).toReal := by
    intro F hF
    unfold nrm2
    have hc : Continuous fun w => ‖F w‖ ^ 2 := by fun_prop
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖F w‖ ^ 2)
      (Filter.Eventually.of_forall fun w => sq_nonneg ‖F w‖) hc.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun w => ?_
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [key _ hf'.cont, key _ hf.cont, hU]

theorem latMove : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b), S.gram = 1 → T.gram = 1 →
    ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    Moves S hS g N → Moves T hT h N' →
    ∀ u' ∈ latO S T (latFr S hS N) (latFr T hT N') (fun _ => True),
      ∃ u ∈ latO S T (intVec D _) (intVec D _) (fun _ => True), actO S T g h u = u' := GlobalTheory.T.unitaryPair_maps_completedHomLattice_onto_translate

theorem latSign : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a)
    (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ g ∈ GfC S, ∀ h ∈ GfC T,
    ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    Moves S hS g N → Moves T hT h N' → ∀ f, IsThetaFunO ψ S T f →
    IsLatVac (heisO ψ S T) (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) f →
    ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
    toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ v, GlobalTheory.AdTh.IsFinOf S T γ v →
    ∀ w, alV D.host.d sc (embH (tauE D) δ (toHom S T hS hT γ)) * heisO ψ S T v f w = f w := GlobalTheory.T.heisenberg_fixes_latticeVacuum_periodLattice

theorem lamPre : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    ∀ x ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N',
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' ∧
      embH (tauE D) δ (toHom S T hS hT γ) = x ∧ ∃ v, GlobalTheory.AdTh.IsFinOf S T γ v := GlobalTheory.T.exists_rationalMatrix_of_mem_periodLattice

theorem fixedLine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a)
    (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ g ∈ GfC S, ∀ h ∈ GfC T,
    ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    Moves S hS g N → Moves T hT h N' → ∀ f, IsThetaFunO ψ S T f →
    IsLatVac (heisO ψ S T) (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) f →
    xiN θ S T hS hT δ sc f ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc)
      (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T a b hS hT δ sc hP g hg h hh N N' hN hN' f hf hl x hx z
  obtain ⟨γ, hγ, rfl, v, hv⟩ := lamPre D S T a b hS hT δ N N' x hx
  have hs := latSign D ψ θ S T a b hS hT δ sc hP g hg h hh N N' hN hN' f hf hl γ hγ v hv
  have hu := GlobalTheory.T.gaussianReading_finiteRationalHeisenbergTranslate D ψ θ S T a b hS hT δ sc hP f hf γ v hv
  rw [← hu]
  simp only [xiN]
  rw [← hs]
  ring

theorem vac_moved : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ f, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) f → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ N N', Moves S hS g N → Moves T hT h N' → IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') (om (g, h) f) ∧ xiN θ S T hS hT δ sc (om (g, h) f) ∈ Formalism.L2.Th1.H.Th (HV sc) (alV D.host.d sc) (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ∧ xiN θ S T hS hT δ sc (om (g, h) f) ≠ 0 := by
  intro D ψ θ S T a b hS hT δ sc hP μ om hW f hf g hg h hh N N' hN hN'
  obtain ⟨hstd, hv⟩ := hf
  have hhol : IsHol θ S T ψ f := ⟨hv.theta, hv.fock⟩
  have hI := GlobalTheory.T.om_pureTensorO_comm D ψ θ S T a b hS hT δ sc hP μ om hW g hg h hh f hhol
  have hth' : IsThetaFunO ψ S T (om (g, h) f) := hW.om_pres _ f hv.theta
  have hvac : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') (om (g, h) f) := by
    refine ⟨hstd, { inf := hv.inf, theta := hth', lat := ?_, fock := hI.1.2, norm := ?_ }⟩
    · refine ⟨fun u' hu' => ?_, fun e he u' hu' hhalf => ?_⟩
      · obtain ⟨u, hu, rfl⟩ := latMove D S T a b hS hT hP.gS hP.gT g hg h hh N N' hN hN' u' hu'
        have h2 : actO S T g h u + actO S T g h u = actO S T g h (u + u) := by
          simp only [actO, Matrix.mul_add, Matrix.add_mul]
        have h3 := hv.lat.1 u hu
        rw [two_nsmul] at h3 ⊢
        rw [h2, ← hW.om_heis g h _ f hv.theta, h3]
      · obtain ⟨u, hu, rfl⟩ := latMove D S T a b hS hT hP.gS hP.gT g hg h hh N N' hN hN' u' hu'
        rw [← hW.om_heis g h u f hv.theta, hv.lat.2 e he u hu (halfBack D S T g h e u hhalf)]
    · refine ⟨hv.norm.1, fun p hp => ?_⟩
      show nrm2 p.1 p.2 (om (g, h) f) = 1
      rw [norm_weilRepresentation_thetaFunction_preserved D ψ S T μ om hW f hv.theta (g, h) p.1 p.2 hp]
      exact hv.norm.2 p hp
  have hne : om (g, h) f ≠ 0 := by
    intro h0
    obtain ⟨p, hp⟩ := hvac.2.norm.1
    have h1 := hvac.2.norm.2 p hp
    rw [h0] at h1
    simp [nrm2] at h1
  have hII := GlobalTheory.T.gaussianTwistedRealReading_entire_and_injective D ψ θ S T a b hS hT δ sc hP
  refine ⟨hvac, ⟨GlobalTheory.SCV.analyticOnNhd_of_differentiable (hII.1 _ hI.1) _,
    fixedLine D ψ θ S T a b hS hT δ sc hP g hg h hh N N' hN hN' _ hth' hvac.2.lat⟩, fun h0 => hne (hII.2 _ hth' h0)⟩

end GlobalTheory.MovedVac
end

section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section

namespace GlobalTheory.MiTop

theorem fixAux {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (hId : GlobalTheory.Core.Mi.IdE X) (S : Set (Fin X.B.I.n → X.B.I.E)) (p : Fin X.B.I.n → X.B.I.E) (hp : p ∈ S)
    (g : GA D (D.sp.Y 0))
    (hg : (iotaX X h g).1 ∈ Formalism.L2.SG.PoincareInHH.HinfS X.B.I S ∧ (iotaX X h g).2 ∈ Formalism.L2.SG.PoincareInHH.HfinS X.B.I S) :
    Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) g) (fun k => Formalism.L2.Theta.incA D (X.ιE (p (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h) k)))) =
      fun k => Formalism.L2.Theta.incA D (X.ιE (p (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h) k))) := by
  have hR := (GlobalTheory.Core.SBesLevi.transport_fix D X.B.I X.ιE hId h (GlobalTheory.Core.Mi.rank_eq X h) S
    (Formalism.IndefR.RationalEmbedding.iota D g)).1 hg
  exact (GlobalTheory.Core.SBesLevi.bridge_fix D g _).2 (hR p hp)

end GlobalTheory.MiTop

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.chartBasePair_datum_rational_approx_eq_twisted : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) g g', g ∈ GfC _ → g' ∈ GfC _ → finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g = ((A.K i (Nat.le_of_succ_le hi) (A.chOf i c)).y ⟨c, rfl⟩).1.1 → finM _ (rankN (I.rec7 l Z) (i + 1) hi) g' = ((A.K (i + 1) hi (A.chOf (i + 1) c')).y ⟨c', rfl⟩).1.1 → ∃ M : ℕ, 0 < M ∧ ∀ (γ γ₀ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → γ₀.map (fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ g⁻¹ g'⁻¹ (γ.map fun r => A.e * incA (I.rec7 l Z) r) + M • v → A.xi i hi (A.chOf i c) (A.chOf (i + 1) c') γ₀ = B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) γ)) := by
  first | exact @GlobalTheory.AdForm.TwResid.tw_resid_datum | exact GlobalTheory.AdForm.TwResid.tw_resid_datum | (intros; apply GlobalTheory.AdForm.TwResid.tw_resid_datum <;> assumption)
end
