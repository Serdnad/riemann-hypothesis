module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle630
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle586
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle577
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairLocalAuxiliaryStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle561
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle617
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SectionTrace.SecOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativity
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses

namespace GlobalTheory.CompanionTheory.LcSplit

theorem level_pick {H : Type} [Group H] [TopologicalSpace H] (σ : H →* H) (hc : Continuous σ) (hi : ∀ g, σ (σ g) = g)
    (K A₁ A₂ : Subgroup H) (f₁ f₂ : H → ℂ) (ho₁ : IsOpen (A₁ : Set H)) (ho₂ : IsOpen (A₂ : Set H)) (hK : A₁ ≤ K)
    (h₁ : IsHecke A₁ f₁) (h₂ : IsHecke A₂ f₂) :
    ∃ L : Subgroup H, IsOpen (L : Set H) ∧ L ≤ K ∧ (∀ k ∈ L, σ k ∈ L) ∧ IsHecke L f₁ ∧ IsHecke L f₂ := by
  have hAo : IsOpen ((A₁ ⊓ A₂ : Subgroup H) : Set H) := by
    rw [Subgroup.coe_inf]; exact ho₁.inter ho₂
  refine ⟨(A₁ ⊓ A₂) ⊓ (A₁ ⊓ A₂).comap σ, ?_, fun x hx => hK hx.1.1, fun k hk => ⟨hk.2, ?_⟩,
    ⟨h₁.1, fun k hk => h₁.2 k hk.1.1⟩, ⟨h₂.1, fun k hk => h₂.2 k hk.1.2⟩⟩
  · rw [Subgroup.coe_inf]
    exact hAo.inter (hAo.preimage hc)
  · show σ (σ k) ∈ A₁ ⊓ A₂
    rw [hi]; exact hk.1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem exists_level (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (hφ₁ : IsTestP φ₁) (hφ₂ : IsTestP φ₂) (w : Pl E) :
    ∃ L : Subgroup (GLw a w × GLw b w), IsOpen (L : Set (GLw a w × GLw b w)) ∧ L ≤ K2 a b w ∧ (∀ k ∈ L, sgP a b w k ∈ L) ∧
      IsHecke L (φ₁ w) ∧ IsHecke L (φ₂ w) := by
  obtain ⟨hc, hi, hk⟩ := sgP_facts E a b w
  obtain ⟨K₁, K₂, hl₁, hl₂, ht⟩ := hφ₁
  obtain ⟨K₁', K₂', hl₁', hl₂', ht'⟩ := hφ₂
  refine level_pick (sgP a b w) hc hi (K2 a b w) ((K₁ w).prod (K₂ w)) ((K₁' w).prod (K₂' w)) _ _ ?_ ?_ ?_ (ht.1 w) (ht'.1 w)
  · rw [Subgroup.coe_prod]; exact (hl₁.1 w).1.prod (hl₂.1 w).1
  · rw [Subgroup.coe_prod]; exact (hl₁'.1 w).1.prod (hl₂'.1 w).1
  · exact Subgroup.prod_mono (hl₁.1 w).2.1 (hl₂.1 w).2.1

theorem fv_split (S : Set (Pl E)) (hS : IsSection S) (w : Pl E) (hw : w ∈ S) (hs : IsSplitAt w)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    fv S φ₁ φ₂ _ y = φ₁ w (evw ⟨w, rfl⟩ y) * φ₂ w (evw ⟨w, rfl⟩ (thv a b _ y)) := by
  unfold fv
  have key : ∀ u : Above (w.under (𝓞 (maximalRealSubfield E))), u.1 ∈ S → u = ⟨w, rfl⟩ := by
    intro u hu
    exact Subtype.ext ((hS w).unique ⟨hu, u.2⟩ ⟨hw, rfl⟩)
  rw [finprod_eq_single _ (⟨w, rfl⟩ : Above (w.under (𝓞 (maximalRealSubfield E))))]
  · rw [finprod_eq_if, if_pos hw, if_pos hs]
  · intro u hu
    rw [finprod_eq_if, if_neg (fun h => hu (key u h))]

theorem th_split (a b : ℕ) (w : Pl E) (hs : IsSplitAt w) :
    (thL a w).prodMap (thL b w) = MonoidHom.id (GLw a w × GLw b w) := by
  unfold thL
  rw [if_pos hs, if_pos hs]
  ext x <;> rfl

theorem seen_split (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (w : Pl E) (hs : IsSplitAt w) :
    seen φ₁ φ₂ w = fun y => hint (K2 a b w) fun z => φ₁ w z * φ₂ w (z⁻¹ * y) := by
  funext y
  unfold seen
  rw [if_pos hs]

theorem locEl_sep {n : ℕ} (w : Pl E) (hs : IsSplitAt w) (δ : GL (Fin n) E) (h : polE δ ∈ Ell E n) :
    (nrmL n w (locEl n w δ)).val.charpoly.Separable := by
  have : (nrmL n w (locEl n w δ)).val.charpoly = (polE δ).map (algebraMap E (w.adicCompletion E)) := by
    unfold nrmL locEl polE
    rw [if_pos hs, if_pos hs]
    exact Matrix.charpoly_map _ _
  rw [this]
  exact h.2.2.1.map

theorem target_side (hU : GlobalTheory.BCT.Unr E) (w : Pl E) (hs : IsSplitAt w)
    (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) (hδ₁ : polE δ₁ ∈ Ell E a) (hδ₂ : polE δ₂ ∈ Ell E b) :
    Good (MonoidHom.id _) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) ∧
    ∀ C : Set (GLw a w × GLw b w), IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (GLw a w × GLw b w)) (locEl a w δ₁, locEl b w δ₂) : Set _)
      (K2 (E := E) a b w : Set (GLw a w × GLw b w)) | ∃ k ∈ K2 (E := E) a b w,
        (Quotient.out q * k)⁻¹ * (locEl a w δ₁, locEl b w δ₂) * MonoidHom.id (GLw a w × GLw b w) (Quotient.out q * k) ∈ C}.Finite := by
  have h1 := GlobalTheory.CompanionTheory.LocGoodProof.locGood E hU a b w (locEl a w δ₁, locEl b w δ₂) (locEl_sep w hs δ₁ hδ₁) (locEl_sep w hs δ₂ hδ₂)
  have h2 := (GlobalTheory.CompanionTheory.TwistOrbit.locSupp E hU a b w (locEl a w δ₁, locEl b w δ₂) (locEl_sep w hs δ₁ hδ₁) (locEl_sep w hs δ₂ hδ₂)).1
  rw [th_split a b w hs] at h1 h2
  exact ⟨h1, h2⟩

theorem pair_integral_points_open_compact (a b : ℕ) (w : Pl E) :
    IsOpen ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) ∧ IsCompact ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) := by
  obtain ⟨hKo₁, hKc₁⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨hKo₂, hKc₂⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  rw [Subgroup.coe_prod]
  exact ⟨hKo₁.prod hKo₂, hKc₁.prod hKc₂⟩

theorem locCompareSplit : LocCompareSplit := by
  intro hCj E _ _ _ hU a b S hS φ₁ φ₂ hφ₁ hφ₂ δ₁ δ₂ hδ₁ hδ₂ w hw hs
  obtain ⟨e, he1, he3, he4, heδ⟩ := GlobalTheory.CompanionTheory.SplitIso.split_iso hCj E a b _ ⟨w, rfl⟩ hs
  obtain ⟨hc, hi, hk⟩ := sgP_facts E a b w
  obtain ⟨L, hLo, hLK, hLs, hH₁, hH₂⟩ := exists_level φ₁ φ₂ hφ₁ hφ₂ w
  obtain ⟨hKo, hKc⟩ := pair_integral_points_open_compact (E := E) a b w
  obtain ⟨hG, hF⟩ := target_side hU w hs δ₁ δ₂ hδ₁ hδ₂
  set y := pv a b (w.under (𝓞 (maximalRealSubfield E))) (ratF E a δ₁, ratF E b δ₂) with hy
  have hN : (e y).1 * sgP a b w (e y).2 = (locEl a w δ₁, locEl b w δ₂) := by
    rw [hy, heδ]
    exact Prod.ext (GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL E a w δ₁ hs) (GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL E b w δ₂ hs)
  have ht := GlobalTheory.EulerTw.Transport.twOrb_transport _ _ e (thv a b _) (swTw (sgP a b w))
    (Kv a b _) ((K2 a b w).prod (K2 a b w)) y (fv S φ₁ φ₂ _) (fun z => φ₁ w z.1 * φ₂ w (sgP a b w z.2))
    he3 he4 (fun g => by
      have h2 : evw ⟨w, rfl⟩ (thv a b _ g) = sgP a b w (e g).2 := by
        rw [← he1, he3]; rfl
      show φ₁ w (e g).1 * φ₂ w (sgP a b w (e g).2) = _
      rw [he1, ← h2, fv_split S hS w hw hs])
  rw [ht, seen_split φ₁ φ₂ w hs, th_split a b w hs]
  have hsc := GlobalTheory.T.twisted_orbital_pair_convolution _ (sgP a b w) (K2 a b w) hc hi hk hKo hKc (e y).1 (e y).2 (φ₁ w) (φ₂ w) L hLo hLK hLs hH₁ hH₂
    (by rw [hN]; exact hG) (by rw [hN]; exact hF)
  rw [hN] at hsc
  exact hsc

end GlobalTheory.CompanionTheory.LcSplit

end
end

section

noncomputable section

open scoped NNReal Matrix TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.StdChart

section Gen

variable {R : Type} [CommRing R] {n : ℕ}

def rx : GL (Fin (n + n)) R ≃* GL (Fin n ⊕ Fin n) R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R (finSumFinEquiv (m := n) (n := n)).symm).toMulEquiv

theorem rx_val (g : GL (Fin (n + n)) R) : (rx g).1 = g.1.submatrix finSumFinEquiv finSumFinEquiv := rfl

theorem rx_inv_val (g : GL (Fin (n + n)) R) :
    ((rx g)⁻¹ : GL (Fin n ⊕ Fin n) R).1 = (g⁻¹ : GL (Fin (n + n)) R).1.submatrix finSumFinEquiv finSumFinEquiv := by
  rw [← map_inv]; rfl

theorem continuous_rx [TopologicalSpace R] : Continuous (rx : GL (Fin (n + n)) R → GL (Fin n ⊕ Fin n) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_submatrix _ _)
  · have : (fun g : GL (Fin (n + n)) R => (((rx g)⁻¹ : GL (Fin n ⊕ Fin n) R) : Matrix _ _ R)) =
        fun g => (g⁻¹ : GL (Fin (n + n)) R).1.submatrix finSumFinEquiv finSumFinEquiv := funext rx_inv_val
    rw [this]
    exact (Units.continuous_coe_inv.matrix_submatrix _ _)

theorem continuous_rx_symm [TopologicalSpace R] :
    Continuous (rx.symm : GL (Fin n ⊕ Fin n) R → GL (Fin (n + n)) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_submatrix _ _)
  · have : (fun g : GL (Fin n ⊕ Fin n) R => (((rx.symm g)⁻¹ : GL (Fin (n + n)) R) : Matrix _ _ R)) =
        fun g => (g⁻¹ : GL (Fin n ⊕ Fin n) R).1.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact (Units.continuous_coe_inv.matrix_submatrix _ _)

theorem form_iff {ι : Type} [Fintype ι] (c : R →+* R) (hc : ∀ x, c (c x) = x) {J : Matrix ι ι R} (hJ : J.map c = J)
    (g : Matrix ι ι R) : Formalism.UG.cT c g * J * g = J ↔ gᵀ * J * g.map c = J := by
  have key : (Formalism.UG.cT c g * J * g).map c = gᵀ * J * g.map c := by
    rw [Matrix.map_mul, Matrix.map_mul, hJ]
    congr 2
    ext i j
    simp [Formalism.UG.cT, hc]
  constructor
  · intro h
    rw [← key, h, hJ]
  · intro h
    have h2 := congrArg (fun M => M.map c) h
    simp only [Matrix.map_mul, hJ] at h2
    have e : (gᵀ).map c = Formalism.UG.cT c g := by ext i j; simp [Formalism.UG.cT]
    have e2 : (g.map c).map c = g := by ext i j; simp [hc]
    rwa [e, e2] at h2

theorem keeps_iff_int {ι : Type} [Fintype ι] [DecidableEq ι] (O : Subring R) (m : GL ι R) :
    (∀ y : ι → R, (∀ i, y i ∈ O) ↔ ∀ i, (m.1 *ᵥ y) i ∈ O) ↔
      ∀ r c, m.1 r c ∈ O ∧ (m⁻¹ : GL ι R).1 r c ∈ O := by
  constructor
  · intro h r c
    have hs : ∀ i, (Pi.single c (1 : R) : ι → R) i ∈ O := fun i => by
      by_cases e : i = c
      · subst e; simp [O.one_mem]
      · simp [e, O.zero_mem]
    refine ⟨by simpa using (h _).1 hs r, ?_⟩
    have h2 := (h (((m⁻¹ : GL ι R).1) *ᵥ Pi.single c 1)).2 (by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact hs) r
    simpa using h2
  · intro h y
    have key : ∀ (M : Matrix ι ι R), (∀ r c, M r c ∈ O) → ∀ y : ι → R, (∀ i, y i ∈ O) → ∀ i, (M *ᵥ y) i ∈ O :=
      fun M hM y hy i => O.sum_mem fun j _ => O.mul_mem (hM i j) (hy j)
    refine ⟨key _ (fun r c => (h r c).1) y, fun hy => ?_⟩
    have := key _ (fun r c => (h r c).2) _ hy
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

end Gen

section Sub

variable {R : Type} {n : ℕ}

theorem sub_inj {X Y : Matrix (Fin (n + n)) (Fin (n + n)) R} :
    X.submatrix finSumFinEquiv finSumFinEquiv = Y.submatrix finSumFinEquiv finSumFinEquiv ↔ X = Y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  ext i j
  have := congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  simpa using this

end Sub

section Std

variable (D : D7) {n : ℕ}

theorem sig_sig (x : D.host.E) : D.sp.cm.sig (D.sp.cm.sig x) = x := by
  have h := isCMExt_host D
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ]
  simp

theorem sigR_sigR (z : AE D) : sigR (AF D.host.F) D.sp.cm.sig (sigR (AF D.host.F) D.sp.cm.sig z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    change a ⊗ₜ[D.host.F] D.sp.cm.sig (D.sp.cm.sig e) = _
    rw [sig_sig]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sigR_inclR (x : D.host.E) :
    sigR (AF D.host.F) D.sp.cm.sig (inclR (AF D.host.F) x) = inclR (AF D.host.F) (D.sp.cm.sig x) := rfl

theorem Jst_map : (GlobalTheory.StdUnn.Jst D n).map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.StdUnn.Jst, GlobalTheory.StdUnn.blk4, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply] <;> split_ifs <;> simp

theorem JR_map : (JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)).map (sigR (AF D.host.F) D.sp.cm.sig) =
    JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n) := by
  ext i j
  simp only [Matrix.map_apply, JR, sigR_inclR]
  rw [← Matrix.map_apply (f := D.sp.cm.sig), Jst_map]

theorem J_eq : (JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)).submatrix finSumFinEquiv finSumFinEquiv =
    Ad.J (AE D) (-1) (Fin n) := by
  have key : ∀ x y, (JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)).submatrix finSumFinEquiv finSumFinEquiv x y =
      inclR (F := D.host.F) (E := D.host.E) (AF D.host.F) ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E) x y) := fun x y => by
    simp only [JR, GlobalTheory.StdUnn.Jst, GlobalTheory.StdUnn.blk4, Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply]
  ext x y
  rw [key]
  rcases x with a | a <;> rcases y with b | b <;> simp [Ad.J, Matrix.one_apply, apply_ite (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))]

variable (χ : (AE D)ˣ →* Circle)

theorem mem_uSub_iff (g : GL (Fin (n + n)) (AE D)) :
    rx g ∈ (adCM D.sp.cm.sig χ).uSub (-1) (Fin n) ↔ g ∈ HR (AF D.host.F) D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) := by
  change (rx g).1ᵀ * Ad.J (AE D) (-1) (Fin n) * (rx g).1.map (sigR (AF D.host.F) D.sp.cm.sig) = Ad.J (AE D) (-1) (Fin n) ↔
    Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) g.1 * JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n) * g.1 = JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)
  rw [form_iff _ (sigR_sigR D) (JR_map D), ← J_eq, rx_val, ← sub_inj (X := _ * _ * _)]
  have : (g.1ᵀ * JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n) * g.1.map (sigR (AF D.host.F) D.sp.cm.sig)).submatrix finSumFinEquiv finSumFinEquiv =
      (g.1.submatrix finSumFinEquiv finSumFinEquiv)ᵀ * (JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)).submatrix finSumFinEquiv finSumFinEquiv *
        (g.1.submatrix finSumFinEquiv finSumFinEquiv).map (sigR (AF D.host.F) D.sp.cm.sig) := by
    rw [← Matrix.submatrix_mul_equiv _ _ finSumFinEquiv finSumFinEquiv finSumFinEquiv,
      ← Matrix.submatrix_mul_equiv _ _ finSumFinEquiv finSumFinEquiv finSumFinEquiv]
    rfl
  rw [this]

def toU (g : GlobalTheory.StdUnn.G D n) : UD D χ n :=
  ⟨rx (matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) g), (mem_uSub_iff D χ _).2 (Subtype.prop (p := (· ∈ HR _ _ _)) g)⟩

theorem toU_val (g : GlobalTheory.StdUnn.G D n) : (toU D χ g).1 = rx (matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) g) := rfl

def ofU (u : UD D χ n) : GlobalTheory.StdUnn.G D n :=
  (⟨rx.symm u.1, (mem_uSub_iff D χ _).1 (by simpa using u.2)⟩ : HR (AF D.host.F) D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n))

theorem ofU_val (u : UD D χ n) : matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) (ofU D χ u) = rx.symm u.1 := rfl

def Psi (n : ℕ) : GlobalTheory.StdUnn.G D n ≃ₜ* UD D χ n where
  toFun := toU D χ
  invFun := ofU D χ
  left_inv g := matHom_injective _ _ _ (by rw [ofU_val, toU_val]; exact rx.symm_apply_apply _)
  right_inv u := Subtype.ext (by rw [toU_val, ofU_val]; exact rx.apply_symm_apply _)
  map_mul' g h := Subtype.ext (by rw [Subgroup.coe_mul, toU_val, toU_val, toU_val, map_mul, map_mul])
  continuous_toFun := (continuous_rx.comp (isEmbedding_matHom _ _ _).continuous).subtype_mk _
  continuous_invFun := (isEmbedding_matHom _ _ _).continuous_iff.2 (continuous_rx_symm.comp continuous_subtype_val)

theorem Psi_val (g : GlobalTheory.StdUnn.G D n) : (Psi D χ n g).1 = rx (matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) g) := rfl

end Std

end GlobalTheory.CompanionTheory.StdChart

end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.ScalWall

open PositivityTheory.RgEis ResidueKilled.Tr GlobalTheory.CompanionTheory.SiegelFrame

theorem pos_eq_norm_cosetSum {G G' : Type} [Group G] [Group G'] (Φ : G ≃* G') (Γ P : Subgroup G) (Γ' P' : Subgroup G')
    (hΓ : ∀ g, g ∈ Γ ↔ Φ g ∈ Γ') (hP : ∀ g, g ∈ P ↔ Φ g ∈ P') (l : G' → ℝ) (hc : Conv Γ' P' l)
    (hl : ∀ γ ∈ Γ', γ ∈ P' → ∀ y, l (γ * y) = l y) (g : G) :
    pos Γ' P' l (Φ g) = ‖GlobalTheory.Eis.cosetSum P Γ (fun x => (Real.exp (l (Φ x)) : ℂ)) g‖ := by
  have hs : HasSum (fun q : PositivityTheory.RgEis.Cos P' Γ' => Real.exp (l (PositivityTheory.RgEis.rep q * Φ g)))
      (PositivityTheory.RgEis.pos Γ' P' l (Φ g)) := (hc (Φ g)).hasSum
  have h2 := GlobalTheory.CompanionTheory.SiegelFrame.hasSum_cos Φ Γ P Γ' P' hΓ hP (fun y => Real.exp (l y))
    (fun γ hγ hγP y => by simp only [hl γ hγ hγP y]) (Φ g) _ hs
  have h3 : HasSum (fun q : PositivityTheory.RgEis.Cos P Γ => ((Real.exp (l (Φ (PositivityTheory.RgEis.rep q * g))) : ℝ) : ℂ))
      ((PositivityTheory.RgEis.pos Γ' P' l (Φ g) : ℝ) : ℂ) :=
    Complex.hasSum_ofReal.mpr (by simpa only [map_mul] using h2)
  have h4 : GlobalTheory.Eis.cosetSum P Γ (fun x => ((Real.exp (l (Φ x)) : ℝ) : ℂ)) g
      = ((PositivityTheory.RgEis.pos Γ' P' l (Φ g) : ℝ) : ℂ) := h3.tsum_eq
  rw [h4, Complex.norm_real, Real.norm_of_nonneg (hs.nonneg fun _ => (Real.exp_pos _).le)]

theorem fin_along {G G' : Type} [Group G] [Group G'] (Φ : G ≃* G') (K' : Subgroup G') (f : G → ℂ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun x => f (x * Φ.symm k)))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun y => f (Φ.symm (y * (k : G'))))) := by
  have e : (Set.range fun k : K' => fun y => f (Φ.symm (y * (k : G'))))
      = (LinearMap.funLeft ℂ ℂ (⇑Φ.symm)) '' (Set.range fun k : K' => fun x => f (x * Φ.symm k)) := by
    rw [← Set.range_comp]
    congr 1
    funext k y
    simp [LinearMap.funLeft_apply, map_mul]
  rw [e, ← Submodule.map_span]
  exact Module.Finite.map _ _

theorem tScal : TScal := by
  unfold ResidueKilled.Tr.TScal ResidueKilled.Tr.Scal
  intro hSec hWL G G' _ _ _ _ _ _ _ _ Φ Γ P Γ' K' P' c η N hK hPar hHt hΓ hP hW f hf hlaw hfin
  have hcrat : ∀ γ ∈ Γ', γ ∈ P' → c γ = 1 := by
    obtain ⟨_, _, ⟨_, _, h, _⟩⟩ := hPar
    exact h
  have hηl : ∀ p ∈ P', ∀ g, η (p * g) = η p + η g := by
    obtain ⟨h, _, _, _⟩ := hHt
    exact h
  have hηr : ∀ γ ∈ Γ', γ ∈ P' → η γ = 0 := by
    obtain ⟨_, _, h, _⟩ := hHt
    exact h
  have hβ : PositivityTheory.RgEis.IsHt Γ' K' P' (fun g => N * η g) := by
    obtain ⟨h1, h2, h3, h4⟩ := hHt
    exact ⟨fun p hp g => by simp only [h1 p hp g, mul_add], fun g k hk => by simp only [h2 g k hk],
      fun γ hγ hγP => by simp only [h3 γ hγ hγP, mul_zero], continuous_const.mul h4⟩
  have hlaw' : ∀ p ∈ P', ∀ x : G', (fun y => f (Φ.symm y)) (p * x)
      = c p * Complex.exp (0 * ↑(η p)) * (fun y => f (Φ.symm y)) x := by
    intro p hp x
    have hp' : Φ.symm p ∈ P := (hP (Φ.symm p)).mpr (by simpa using hp)
    simp only [map_mul, zero_mul, Complex.exp_zero, mul_one]
    rw [hlaw _ hp']
    simp
  have hfin' := fin_along Φ.toMulEquiv K' f hfin
  obtain ⟨R, D, H, hD, hDz, hHd, hHc, hconv1, hconv2, hbd, hsum⟩ :=
    GlobalTheory.CompanionTheory.SiegelFrame.scalar_wall hSec hWL Γ' K' P' c η (fun g => N * η g) hK hPar hHt hβ hW
      (fun y => f (Φ.symm y)) 0 (hf.comp (map_continuous Φ.symm)) hlaw' hfin'
  refine ⟨D, fun z g => H z (Φ g), R, hD, hDz, fun g => hHd (Φ g), ?_, ?_, ?_⟩
  · exact hHc.comp (continuous_fst.prodMk ((map_continuous Φ).comp continuous_snd))
  · intro z hz g
    show H z (Φ g) = _
    have h2 := GlobalTheory.CompanionTheory.SiegelFrame.hasSum_cos Φ.toMulEquiv Γ P Γ' P' hΓ hP
      (fun y => D z * (Complex.exp ((z - 0) * ↑(η y)) * f (Φ.symm y)))
      (fun γ hγ hγP y => by
        have hγ' : Φ.symm γ ∈ P := (hP (Φ.symm γ)).mpr (by simpa using hγP)
        simp only [hηl γ hγP y, hηr γ hγ hγP, zero_add, map_mul]
        rw [hlaw _ hγ']
        simp [hcrat γ hγ hγP])
      (Φ g) _ (hsum z hz (Φ g))
    have h3 : HasSum (fun q : PositivityTheory.RgEis.Cos P Γ =>
        D z * (Complex.exp (z * ↑(η (Φ (PositivityTheory.RgEis.rep q * g)))) * f (PositivityTheory.RgEis.rep q * g))) (H z (Φ g)) := by
      have e : (fun q : PositivityTheory.RgEis.Cos P Γ =>
          D z * (Complex.exp (z * ↑(η (Φ (PositivityTheory.RgEis.rep q * g)))) * f (PositivityTheory.RgEis.rep q * g)))
          = fun q => (fun y => D z * (Complex.exp ((z - 0) * ↑(η y)) * f (Φ.symm y)))
              (Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g) := by
        funext q
        have hm : Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g = Φ (PositivityTheory.RgEis.rep q * g) :=
          (map_mul Φ _ _).symm
        show _ = D z * (Complex.exp ((z - 0) * ↑(η (Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g)))
          * f (Φ.symm (Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g)))
        rw [hm, sub_zero, ContinuousMulEquiv.symm_apply_apply]
      rw [e]
      exact h2
    rw [← h3.tsum_eq, tsum_mul_left]
    rfl
  · intro a b ha hb
    obtain ⟨M, hM⟩ := hbd a b ha hb
    refine ⟨M, fun z hz1 hz2 g => ?_⟩
    have hl2 : (fun x : G' => N * η x - b * η x) = fun x => (N - b) * η x := by
      funext x
      ring
    have hinv : ∀ (t : ℝ), ∀ γ ∈ Γ', γ ∈ P' → ∀ y, t * η (γ * y) = t * η y := by
      intro t γ hγ hγP y
      rw [hηl γ hγP y, hηr γ hγ hγP, zero_add]
    have e1 : PositivityTheory.RgEis.pos Γ' P' (fun x => a * η x) (Φ g)
        = ‖GlobalTheory.Eis.cosetSum P Γ (fun x => ((Real.exp (a * η (Φ x)) : ℝ) : ℂ)) g‖ :=
      pos_eq_norm_cosetSum Φ.toMulEquiv Γ P Γ' P' hΓ hP (fun x => a * η x) (hconv1 a ha)
      (fun γ hγ hγP y => hinv a γ hγ hγP y) g
    have hc2 : PositivityTheory.RgEis.Conv Γ' P' (fun x => (N - b) * η x) := by
      rw [← hl2]
      exact hconv2 b hb
    have e2 : PositivityTheory.RgEis.pos Γ' P' (fun x => (N - b) * η x) (Φ g)
        = ‖GlobalTheory.Eis.cosetSum P Γ (fun x => ((Real.exp ((N - b) * η (Φ x)) : ℝ) : ℂ)) g‖ :=
      pos_eq_norm_cosetSum Φ.toMulEquiv Γ P Γ' P' hΓ hP (fun x => (N - b) * η x) hc2
      (fun γ hγ hγP y => hinv (N - b) γ hγ hγP y) g
    have key := hM z hz1 hz2 (Φ g)
    have e3 : PositivityTheory.RgEis.pos Γ' P' (fun x => N * η x - b * η x) (Φ g)
        = PositivityTheory.RgEis.pos Γ' P' (fun x => (N - b) * η x) (Φ g) := by
      rw [hl2]
    calc ‖H z (Φ g)‖ ≤ M * (PositivityTheory.RgEis.pos Γ' P' (fun x => a * η x) (Φ g)
          + PositivityTheory.RgEis.pos Γ' P' (fun x => N * η x - b * η x) (Φ g)) := key
      _ = _ := by
        rw [e3, e1, e2]
        try rfl

end GlobalTheory.CompanionTheory.ScalWall

end
end
