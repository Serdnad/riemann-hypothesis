module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Mathlib.Algebra.DirectSum.LinearMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle017
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem lastPos_of_kapIs {D : D7} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} (h : KapIs κ) (i : Fin D.R.m) :
    (κ i).LastPos := by
  intro τ a ha
  rw [(h i τ).1 a, show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (inR i).1 (inR i).2 _]
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have hs : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + ((i : ℕ) + 1) - 1 := rfl
  have h1 : ¬ (a : ℕ) < D.R.k - 1 := by omega
  have h2 : (a : ℕ) - (D.R.k - 1) < D.R.m := by omega
  have h3 : (⟨(a : ℕ) - (D.R.k - 1), h2⟩ : Fin D.R.m) = i := Fin.ext (by show (a : ℕ) - (D.R.k - 1) = i; omega)
  have h4 : (((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) = (a : ℕ) + 1 := by exact_mod_cast ha.symm
  have h5 := (D.hc τ).gap_be i
  simp only [aPl, if_pos a.2, Formalism.L2.NTheta.lamAt, dif_neg h1, dif_pos h2, h3, h4]
  rw [Int.le_toNat (Int.floor_nonneg.2 (by linarith)), Int.le_floor]
  push_cast
  linarith

theorem lastPos_wtA_of_pins {D : D7} (Q : Par D) (h : Q.Pins) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) (hw : w.LastPos) :
    Formalism.L2.Pj.LastPos (Q.Dw j) (wtA w) := by
  intro τ hτ hm
  obtain ⟨t, rfl⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi Q h.1 τ hτ
  have hmult : (Q.Dw j).mult (DV.tauEmb D t) = (D.R.sigW j).1 := by
    unfold Datum.mult
    have hτ' : (DV.tauEmb D t) (Q.H.rt : D.host.E) = Q.H.rt0 := hτ
    rw [if_pos hτ']
    exact (h.2.2.2 j hj).1
  rw [hmult] at hm ⊢
  have h1 : 1 ≤ w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := hw t _ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  have h2 : ext0 (w.aP t) ((D.R.sigW j).1 - 1) = w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := by
    unfold ext0
    rw [dif_pos (by omega)]
  unfold wtA
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
  simp only [if_true]
  omega

section Frame

variable {D : D7} {W : HSp D} {S : D.what₂.Tau → Finset (ℚ × Bool)} (M : Formalism.IndefR.Mult.DSModel W S) {r : ℕ} (hr : W.rank = r)
  (X : Data D.host.E r) {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {p : ℕ}

theorem isInvOf_cart (hx : IsModelBaseFrameFamily M hr x₀) (hp : X.p0 + p = r) (hε : ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < p)) :
    IsInvOf W hr X (fun τ => x₀ τ.1) (cart M) := by
  intro ρ τ hτ
  have hq : nNeg (M.ε ρ) = X.p0 := (nNeg_shape (by omega) (hε ρ)).trans (by omega)
  have e : mat (Ψ := X.Ψ) (fun τ => x₀ τ.1) τ = x₀ (tauE D ρ) := by rw [← hτ]; rfl
  rw [e, hx.mul, cart, Formalism.REAL.Jm, torus_x0Mat, hx ρ]
  ext a c
  have hc := c.2
  simp only [sgnM, Matrix.neg_apply, mul_diagonal, reindex_apply, submatrix_apply, hε, hq, arr, sgn,
    finCongr_symm, finCongr_apply, Fin.val_cast]
  split_ifs with h1 h2 h3
  all_goals first | (simp at *; omega) | simp

theorem isBasOf_onb (hx : IsModelBaseFrameFamily M hr x₀) (hp : X.p0 + p = r) (hε : ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < p)) :
    IsBasOf W hr X hp (fun τ => x₀ τ.1) (onb M) := by
  intro ρ τ hτ k i a hi
  have hq : nNeg (M.ε ρ) = X.p0 := (nNeg_shape (by omega) (hε ρ)).trans (by omega)
  show _ = x₀ τ.1 _ _
  rw [hτ, hx ρ]
  simp only [x0Mat, reindex_apply, submatrix_apply, hq, finCongr_symm, finCongr_apply, id, Fin.cast_cast, Fin.cast_eq_self]
  congr 1
  apply Fin.ext
  rw [hi]
  rcases k with k | k
  · have hk := k.2
    have h1 : ((rowIdx hp (Sum.inl k) : Fin r) : ℕ) = X.p0 + k := by simp [rowIdx]
    unfold arr
    split_ifs with h
    · simp only [Fin.val_cast, h1] at h; omega
    · simp only [Fin.val_cast, h1, Sum.elim_inl]; omega
  · have hk := k.2
    have h1 : ((rowIdx hp (Sum.inr k) : Fin r) : ℕ) = X.p0 - (k + 1) := by simp [rowIdx]
    unfold arr
    split_ifs with h
    · simp only [Fin.val_cast, h1, Sum.elim_inr]; omega
    · simp only [Fin.val_cast, h1] at h; omega

end Frame


end GlobalTheory.AdTh
end

section

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AdTh
variable {D : D7} {r g : ℕ}

theorem isMod_of (W : HSp D) (hr : W.rank = r) (X : Data D.host.E r) (hm : Formalism.L2.Pj.ModelW W hr X)
    (hp : ∀ ρ, tauE D ρ ∈ X.Ψ) : IsMod W hr X := by
  have hpsi : ∀ τ : D.host.E →+* ℂ, τ ∈ X.Ψ ↔ ∃ ρ, τ = tauE D ρ := by
    intro τ
    refine ⟨fun h => ?_, fun ⟨ρ, h⟩ => h ▸ hp ρ⟩
    have h1 := (X.cmType τ).1 h
    obtain ⟨ρ, hρ⟩ := (GlobalTheory.StdRat.tauE_cm D τ).2 (fun ⟨ρ, hρ⟩ => h1 (hρ ▸ hp ρ))
    exact ⟨ρ, hρ.symm⟩
  obtain ⟨ρ⟩ : Nonempty D.what₂.Tau := by
    by_contra hne
    have h := GlobalTheory.StdRat.tauE_cm D D.host.φ₀
    obtain ⟨ρ, -⟩ := h.2 (fun ⟨ρ, _⟩ => hne ⟨ρ⟩)
    exact hne ⟨ρ⟩
  refine ⟨hm, hpsi, ?_⟩
  have h1 := X.κ0_sign ⟨tauE D ρ, hp ρ⟩
  have h2 := xi_zero_im_pos D ρ
  rcases X.κ0_xi with h | h
  · rw [h, hm.2]; ring
  · exfalso
    rw [h, hm.2] at h1
    simp [map_ofNat] at h1
    linarith

end GlobalTheory.AdTh
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntMatOpen

open IsDedekindDomain.HeightOneSpectrum

def intLat (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {X | ∀ i j, Valued.v (X i j) ≤ 1}
  add_mem' {X Y} hX hY i j := (Valued.v.map_add (X i j) (Y i j)).trans (max_le (hX i j) (hY i j))
  zero_mem' i j := by simp
  neg_mem' {X} hX i j := by simpa using hX i j

theorem coe_intLat (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) :
    (intLat E w a b : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) =
      Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin b =>
        (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
  ext X
  constructor
  · intro h i _ j _
    exact h i j
  · intro h i j
    exact h i trivial j trivial

theorem intMat_open_compact : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ), ∃ Λ : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (Λ : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ IsCompact (Λ : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ intMat a b w = AddSubgroup.toSubgroup Λ := by
  intro E _ _ w a b
  refine ⟨intLat E w a b, ?_, ?_, ?_⟩
  · rw [coe_intLat]
    exact isOpen_set_pi Set.finite_univ fun i _ => isOpen_set_pi Set.finite_univ fun j _ =>
      Valued.isOpen_valuationSubring _
  · rw [coe_intLat]
    exact isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
      PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w
  · have hS : {X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) |
        ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1} =
        ((AddSubgroup.toSubgroup (intLat E w a b) : Subgroup _) : Set _) := by
      ext X; rfl
    unfold intMat
    rw [hS, Subgroup.closure_eq]

end GlobalTheory.IntMatOpen
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_iSup_eq_sum : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) [Fintype ι] (M : ι → Submodule ℂ V)
    (L : V →ₗ[ℂ] V), iSupIndep M → (∀ i, FiniteDimensional ℂ (M i)) → (∀ i, ∀ v ∈ M i, L v ∈ M i) →
    trOn (⨆ i, M i) L = ∑ i, trOn (M i) L := by
  intro V _ _ ι _ M L hind hfin hinv
  haveI := hfin
  have hp : (⨆ i, M i) = ⨆ i ∈ (Finset.univ : Finset ι), M i := by simp
  have hs : iSupIndep (fun i : (Finset.univ : Finset ι) ↦ M i) :=
    hind.comp Subtype.val_injective
  have hf : ∀ i, Set.MapsTo L (M i) (M i) := fun i v hv ↦ hinv i v hv
  have hsup : ∀ v ∈ (⨆ i, M i), L v ∈ (⨆ i, M i) := by
    intro v hv
    refine Submodule.iSup_induction M (motive := fun v ↦ L v ∈ ⨆ i, M i) hv ?_ ?_ ?_
    · intro i x hx; exact Submodule.mem_iSup_of_mem i (hinv i x hx)
    · simp
    · intro x y hx hy; rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  have key := LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup (N := M) Finset.univ hs hf
    (⨆ i, M i) hp hsup
  unfold trOn
  rw [dite_eq_left hsup, key]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dite_eq_left (hinv i)]

end GlobalTheory.BCT
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.CartanConjSkew

open scoped Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem exists_mat_at {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {m k : Type} (z : InfinitePlace F → Matrix m k ℂ) :
    ∃ u : Matrix m k (AE F E), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = z w := by
  choose a ha using fun i j => GlobalTheory.PolRangeInf.exists_at_inf_values hcm τ (fun w => z w i j)
  refine ⟨Matrix.of a, fun x hx => ?_, fun w => ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact (ha i j).1 x hx
  · ext i j
    simp [(ha i j).2 w]

theorem mat_eq_zero {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {m k : Type} (D : Matrix m k (AE F E)) (hD : At (evI F) D) (h0 : ∀ w, D.map (piInf (τ w)) = 0) : D = 0 := by
  ext i j
  refine GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hcm τ (D i j) (fun u hu => ?_) (fun w => ?_)
  · have := congrFun (congrFun (hD u hu) i) j
    simpa using this
  · have := congrFun (congrFun (h0 w) i) j
    simpa using this

theorem at_add {m k : Type} {D D' : Matrix m k (AE F E)} (hD : At (evI F) D) (hD' : At (evI F) D') :
    At (evI F) (D + D') := by
  intro u hu; rw [smul_add, hD u hu, hD' u hu, add_zero]

theorem at_mul_left {m k l : Type} [Fintype k] {D : Matrix m k (AE F E)} (hD : At (evI F) D) (N : Matrix k l (AE F E)) :
    At (evI F) (D * N) := by
  intro u hu; rw [← Matrix.smul_mul, hD u hu, Matrix.zero_mul]

theorem at_mul_right {m k l : Type} [Fintype k] {D : Matrix k l (AE F E)} (hD : At (evI F) D) (N : Matrix m k (AE F E)) :
    At (evI F) (N * D) := by
  intro u hu; rw [← Matrix.mul_smul, hD u hu, Matrix.mul_zero]

theorem at_transpose {m k : Type} {D : Matrix m k (AE F E)} (hD : At (evI F) D) : At (evI F) Dᵀ := by
  intro u hu; rw [← Matrix.transpose_smul, hD u hu, Matrix.transpose_zero]

theorem at_map_cA (σ : E →ₐ[F] E) {m k : Type} {D : Matrix m k (AE F E)} (hD : At (evI F) D) :
    At (evI F) (D.map (cA σ)) := by
  intro u hu
  ext i j
  have := congrFun (congrFun (hD u hu) i) j
  simp only [Matrix.smul_apply, Matrix.zero_apply, Matrix.map_apply] at this ⊢
  rw [← map_smul, this, map_zero]

theorem map_cA_piInf {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {m k : Type}
    (D : Matrix m k (AE F E)) : (D.map (cA σ)).map (piInf τ) = (D.map (piInf τ)).map star := by
  ext i j
  simp [GlobalTheory.RealLift.KLineProof.piInf_cA hcm]

theorem cartan_conj {n r s : ℕ} (M θ₁ θ₂ : Matrix (Fin n) (Fin n) ℂ) (hs : HasSig M r s) (h₁ : IsCartan M θ₁)
    (h₂ : IsCartan M θ₂) :
    ∃ u v : Matrix (Fin n) (Fin n) ℂ, u * v = 1 ∧ uᵀ * M * u.map star = M ∧ u * θ₁ = θ₂ * u := by
  obtain ⟨A₁, hF₁, hA₁⟩ := GlobalTheory.T.cartanEigen_orthonormalFrame_exists n r s M θ₁ hs h₁
  obtain ⟨A₂, hF₂, hA₂⟩ := GlobalTheory.T.cartanEigen_orthonormalFrame_exists n r s M θ₂ hs h₂
  obtain ⟨A₁', h11, h12⟩ := GlobalTheory.RealLift.KLineProof.frame_inv hF₁
  obtain ⟨A₂', h21, h22⟩ := GlobalTheory.RealLift.KLineProof.frame_inv hF₂
  refine ⟨A₂ * A₁', A₁ * A₂', ?_, ?_, ?_⟩
  · calc A₂ * A₁' * (A₁ * A₂') = A₂ * (A₁' * A₁) * A₂' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h12, Matrix.mul_one, h21]
  · have e1 := hF₁.1
    have e2 := hF₂.1
    rw [Matrix.transpose_mul, GlobalTheory.RealLift.KLineProof.map_star_mul]
    calc A₁'ᵀ * A₂ᵀ * M * (A₂.map star * A₁'.map star)
        = A₁'ᵀ * (A₂ᵀ * M * A₂.map star) * A₁'.map star := by simp only [Matrix.mul_assoc]
      _ = A₁'ᵀ * (A₁ᵀ * M * A₁.map star) * A₁'.map star := by rw [e2, e1]
      _ = (A₁ * A₁')ᵀ * M * (A₁ * A₁').map star := by
          rw [Matrix.transpose_mul, GlobalTheory.RealLift.KLineProof.map_star_mul]; simp only [Matrix.mul_assoc]
      _ = M := by
          rw [h11, Matrix.transpose_one, Matrix.map_one _ (star_zero _) (star_one _), Matrix.one_mul, Matrix.mul_one]
  · have k1 : A₁' * θ₁ = Formalism.BasicNotions.TH.Jm r s * A₁' := by
      calc A₁' * θ₁ = A₁' * θ₁ * (A₁ * A₁') := by rw [h11, Matrix.mul_one]
        _ = A₁' * (θ₁ * A₁) * A₁' := by simp only [Matrix.mul_assoc]
        _ = (A₁' * A₁) * Formalism.BasicNotions.TH.Jm r s * A₁' := by rw [hA₁]; simp only [Matrix.mul_assoc]
        _ = Formalism.BasicNotions.TH.Jm r s * A₁' := by rw [h12, Matrix.one_mul]
    calc A₂ * A₁' * θ₁ = A₂ * (A₁' * θ₁) := Matrix.mul_assoc _ _ _
      _ = A₂ * Formalism.BasicNotions.TH.Jm r s * A₁' := by rw [k1, Matrix.mul_assoc]
      _ = θ₂ * (A₂ * A₁') := by rw [← hA₂, Matrix.mul_assoc]

end GlobalTheory.CartanConjSkew

namespace GlobalTheory.CartanConjSkew

open scoped Matrix

theorem conj_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n r s : ℕ) (X Y : Spc F E n), B.IsGood σ → X.IsSkew σ B r s → (reS X Y).IsSkew σ B r s →
    ∃ g ∈ UAt σ X (evI F), ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)) := by
  intro F E _ _ _ _ _ σ B n r s X Y hB hX hY
  have hcm := hB.cm
  have key : ∀ w, ∃ u v : Matrix (Fin n) (Fin n) ℂ, u * v = 1 ∧
      uᵀ * X.J.map (B.emb w).1 * u.map star = X.J.map (B.emb w).1 ∧ u * X.θ w = Y.θ w * u := by
    intro w
    obtain ⟨u, v, huv, hu, hθ⟩ := cartan_conj (Complex.I • X.J.map (B.emb w).1) (X.θ w) (Y.θ w) (hX.sig w)
      (hX.cartan w) (hY.cartan w)
    refine ⟨u, v, huv, ?_, hθ⟩
    rw [Matrix.mul_smul, Matrix.smul_mul] at hu
    exact smul_right_injective _ Complex.I_ne_zero hu
  choose u v huv hu hθ using key
  obtain ⟨G, hGat, hG⟩ := exists_mat_at hcm B.emb (fun w => u w - 1)
  obtain ⟨H, hHat, hH⟩ := exists_mat_at hcm B.emb (fun w => v w - 1)
  have hmap1 : ∀ w, (1 : Matrix (Fin n) (Fin n) (AE F E)).map (piInf (B.emb w)) = 1 :=
    fun w => Matrix.map_one _ (map_zero _) (map_one _)
  have hgmap : ∀ w, (1 + G).map (piInf (B.emb w)) = u w := by
    intro w; rw [Matrix.map_add _ (map_add _), hmap1, hG]; abel
  have hhmap : ∀ w, (1 + H).map (piInf (B.emb w)) = v w := by
    intro w; rw [Matrix.map_add _ (map_add _), hmap1, hH]; abel
  have hgh : (1 + G) * (1 + H) = 1 := by
    have h0 : (1 + G) * (1 + H) - 1 = 0 := by
      apply mat_eq_zero hcm B.emb
      · have e : (1 + G) * (1 + H) - 1 = G + H + G * H := by noncomm_ring
        rw [e]; exact at_add (at_add hGat hHat) (at_mul_left hGat H)
      · intro w
        rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, hgmap, hhmap, hmap1, huv, sub_self]
    exact sub_eq_zero.1 h0
  have hhg : (1 + H) * (1 + G) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hgh
  let g0 : GL (Fin n) (AE F E) := ⟨1 + G, 1 + H, hgh, hhg⟩
  have hmem : g0 ∈ UG (cA σ) (incM F X.J) := by
    show (1 + G)ᵀ * incM F X.J * (1 + G).map (cA σ) = incM F X.J
    have h0 : (1 + G)ᵀ * incM F X.J * (1 + G).map (cA σ) - incM F X.J = 0 := by
      apply mat_eq_zero hcm B.emb
      · have e : (1 + G)ᵀ * incM F X.J * (1 + G).map (cA σ) - incM F X.J =
            Gᵀ * incM F X.J + incM F X.J * G.map (cA σ) + Gᵀ * incM F X.J * G.map (cA σ) := by
          rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_add, Matrix.transpose_one]
          noncomm_ring
        rw [e]
        exact at_add (at_add (at_mul_left (at_transpose hGat) _) (at_mul_right (at_map_cA σ hGat) _))
          (at_mul_right (at_map_cA σ hGat) _)
      · intro w
        rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_cA_piInf hcm, hgmap,
          incM_map_piInf, hu, sub_self]
    exact sub_eq_zero.1 h0
  refine ⟨⟨g0, hmem⟩, ?_, fun w => ?_⟩
  · show At (evI F) ((1 + G) - 1)
    rw [add_sub_cancel_left]; exact hGat
  · show (1 + G).map (piInf (B.emb w)) * X.θ w = Y.θ w * (1 + G).map (piInf (B.emb w))
    rw [hgmap]; exact hθ w

end GlobalTheory.CartanConjSkew
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)


theorem _root_.GlobalTheory.T.skew_adapted_pair_restriction_theta : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∃ L : Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
        Module.finrank F L = Fintype.card (Fin n × Fin d) ∧
        ∀ (t : AF F), ∀ w ∈ L, ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))), ∃ z : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
          (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
            schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
              M.co.rho B.ψ u (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) φ) := by
  first | exact @GlobalTheory.MixedLagr.exists_ratLagr | exact GlobalTheory.MixedLagr.exists_ratLagr | (intros; apply GlobalTheory.MixedLagr.exists_ratLagr <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_holomorphic_charts_genericPoint_projective : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∃ U : X.Opens, genericPoint X ∈ U ∧ ∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source := by
  first | exact @GlobalTheory.GenericCharts.exists_generic_charts | exact GlobalTheory.GenericCharts.exists_generic_charts | (intros; apply GlobalTheory.GenericCharts.exists_generic_charts <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mem_primitiveSubmodule_of_isCan_of_rigToExt_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (x : G.RigExt),
      GlobalTheory.PtExt.IsCan t c x → G.rigToExt x = 0 → c ∈ PrimitiveSubmodule A :=
  @GlobalTheory.PtExt.mem_F1prim_of_rigToExt_eq_zero_of_pow_eq_zero
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

theorem _root_.GlobalTheory.T.exists_affine_etale_coordinates_generic_point : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ ∃ t : Fin D → Γ(X, U), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) t).Etale := by
  first | exact @GlobalTheory.GenericCoords.exists_affine_etale_coords | exact GlobalTheory.GenericCoords.exists_affine_etale_coords | (intros; apply GlobalTheory.GenericCoords.exists_affine_etale_coords <;> assumption)
end
