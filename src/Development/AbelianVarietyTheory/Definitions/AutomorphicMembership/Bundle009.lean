module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemberFormsNonempty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle017
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

namespace GlobalTheory.Mem.PreXModel

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem embLL_tauLL (B : Base) (τ : Tau B.R) : B.embLL.comp (B.tauLL τ) = B.host.emb τ := by
  unfold Base.tauLL Host.emb
  rw [← RingHom.comp_assoc, B.embE_φ₀]

end GlobalTheory.Mem.PreXModel

end
end

section

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure GJStage (B : Base) (C : Cols B) where
  vol : @HSpace B.host.E _ _ B.host.cmStar → ℝ
  vol_pos : ∀ W, 0 < vol W
  cd : CDHaar
  jet : ThetaJet B.R B.host
  jetU : jet.Sit → B.Word
  jetL : ∀ i, (C.mem (jetU i)).C.cls (jet.jOf i - 1)
  jetL' : ∀ i, (C.mem (jetU i)).C.cls (jet.jOf i)
  jetW : jet.Sit → B.places.Pl
  jetW_l : ∀ i, B.places.resChar (jetW i) = (jet.loc i).l
  jetTau : ∀ i, ZMod (jet.loc i).d → (Tau B.R)
  jetW1 : jet.Sit1 → B.places.Pl
  resChar_thetaJetPlaceDegOne : ∀ i, B.places.resChar (jetW1 i) = (jet.loc1 i).l
  jetTau1 : jet.Sit1 → (Tau B.R)
  jetU1 : jet.Sit1 → B.Word
  jetL1 : ∀ i, (C.mem (jetU1 i)).C.cls (jet.j1Of i - 1)
  jetL1' : ∀ i, (C.mem (jetU1 i)).C.cls (jet.j1Of i)
  gx : GlobalExtra B.LL (Tau B.R)
  gat : ∀ u (w : B.places.Pl), GIdx B.host (C.mem u).A.T (B.places.resChar w) →
    Formalism.MainNotions.G.GAtP (B.places.resChar w)
  gat_d : ∀ u w h, (gat u w h).d = Module.finrank ℂ (C.mem u).A.Mu0

end GlobalTheory.Mem

end
end

section

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure RowsRest (B : Base) (C : Cols B) where
  muAt : B.places.Pl → C.Tup
  muAt_conj : ∀ w, muAt (B.places.conj w) = muAt w
  muTw : B.places.Pl → C.Tup
  muTw_conj : ∀ w, muTw (B.places.conj w) = muTw w
  muAt_or : ∀ w, muAt w = C.mu0 ∨ muAt w = muTw w
  EE : Type
  [instEE : NormedAddCommGroup EE]
  [instEEi : InnerProductSpace ℂ EE]
  [instEEf : FiniteDimensional ℂ EE]
  Drows : ℕ
  onb : OrthonormalBasis (Fin Drows) ℂ EE
  Dall : ℕ
  delp : ℝ
  delp_le_one : delp ≤ 1
  D_eq : (Drows : ℝ) = (1 - delp) * Dall
  EE0 : Type
  [instEE0 : NormedAddCommGroup EE0]
  [instEE0i : InnerProductSpace ℂ EE0]
  [instEE0f : FiniteDimensional ℂ EE0]
  D0 : ℕ
  onb0 : OrthonormalBasis (Fin D0) ℂ EE0
  FT : Type
  [instFT : Fintype FT]
  [instFTd : DecidableEq FT]
  ft : Fin Drows → FT
  ft0 : Fin D0 → FT
  Amb : C.Tup → Type
  [instAmb : ∀ μ, NormedAddCommGroup (Amb μ)]
  [instAmbi : ∀ μ, InnerProductSpace ℂ (Amb μ)]
  [instAmbf : ∀ μ, FiniteDimensional ℂ (Amb μ)]
  Mult : C.Tup → ℕ → Type
  [instMult : ∀ μ j, NormedAddCommGroup (Mult μ j)]
  [instMulti : ∀ μ j, InnerProductSpace ℂ (Mult μ j)]
  [instMultf : ∀ μ j, FiniteDimensional ℂ (Mult μ j)]
  multZero : ∀ μ, Mult μ 0 ≃ₗᵢ[ℂ] EE
  multTop : ∀ μ, Mult μ B.R.m ≃ₗᵢ[ℂ] Amb μ
  io : ∀ μ j, Mult μ (j + 1) →ₗ[ℂ] Mult μ j
  Mtilde : ∀ μ, Rows.OLat B.O (B.embLL.comp B.OtoLL) (Amb μ)
  eOp : ∀ μ, Amb μ →ₗ[ℂ] Amb μ
  eOp_idem : ∀ μ, eOp μ ∘ₗ eOp μ = eOp μ
  eOp_sa : ∀ μ, (eOp μ).IsSymmetric
  Mu : B.Word → Type
  [instMu : ∀ u, NormedAddCommGroup (Mu u)]
  [instMui : ∀ u, InnerProductSpace ℂ (Mu u)]
  [instMuf : ∀ u, FiniteDimensional ℂ (Mu u)]
  perCol : ∀ u (μ : C.Tup), Mu u → Amb μ → ℂ
  Bu : ∀ u, Mu u → EE → ℂ
  ze : B.Word → C.Tup → B.LLˣ
  rowsRest_wordColumnUnit_baseTuple : ∀ u, ze u C.mu0 = 1
  Mj : ℕ → Type
  [instMj : ∀ j, NormedAddCommGroup (Mj j)]
  [instMji : ∀ j, InnerProductSpace ℂ (Mj j)]
  [instMjf : ∀ j, FiniteDimensional ℂ (Mj j)]
  MjLat : ∀ j, Rows.OLat B.O (B.embLL.comp B.OtoLL) (Mj j)
  kaBig : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ
  kaSmall : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ
  Mt : C.Tup → ℕ → Type
  [instMt : ∀ μ j, NormedAddCommGroup (Mt μ j)]
  [instMti : ∀ μ j, InnerProductSpace ℂ (Mt μ j)]
  [instMtf : ∀ μ j, FiniteDimensional ℂ (Mt μ j)]
  MtLat : ∀ μ j, Rows.OLat B.O (B.embLL.comp B.OtoLL) (Mt μ j)
  MtL : C.Tup → ℕ → Type
  [instMtL : ∀ μ j, AddCommGroup (MtL μ j)]
  [instMtLm : ∀ μ j, Module B.LL (MtL μ j)]
  jMt : ∀ μ j, MtL μ j →ₛₗ[B.embLL] Mt μ j
  jMt_basis : ∀ μ j, ∀ b : Module.Basis (Module.Free.ChooseBasisIndex B.LL (MtL μ j)) B.LL (MtL μ j),
    LinearIndependent ℂ (fun i => jMt μ j (b i)) ∧ Submodule.span ℂ (Set.range (fun i => jMt μ j (b i))) = ⊤
  MtLat_sub : ∀ μ j, ∀ x ∈ (MtLat μ j).gen, x ∈ Set.range (jMt μ j)
  eMt : ∀ μ j, Mt μ j →ₗ[ℂ] Mt μ j
  eMt_idem : ∀ μ j, eMt μ j ∘ₗ eMt μ j = eMt μ j
  eMt_sa : ∀ μ j, (eMt μ j).IsSymmetric
  eMt_LL : ∀ μ j (x : MtL μ j), ∃ y : MtL μ j, jMt μ j y = eMt μ j (jMt μ j x)
  thetaP : ∀ μ j, Mt μ j →ₗ[ℂ] Mj j
  isot : ∀ j, FT → Submodule ℂ (Mj j)
  lamP : C.Tup → ℕ → FT → ℝ
  Ij : C.Tup → ℕ → B.places.Pl → ℤ
  jw : C.Tup → ℕ → B.places.Pl → ℤ
  etaJ : ℕ → B.places.Pl → ℚ
  etaJ_nonneg : ∀ j w, 0 ≤ etaJ j w
  shaLen : ℕ → ℕ → ℚ
  shaLen_nonneg : ∀ l e, 0 ≤ shaLen l e
  eMu : ∀ u, Mu u ≃ₗ[ℂ] (C.mem u).A.Mram
  eMt0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] Amb C.mu0
  perCol_base_eq_PtilCol : ∀ u (φ : Mu u) (F : Amb C.mu0),
    perCol u C.mu0 φ F = (C.mem u).P.PtilCol ((eMu u φ : (C.mem u).A.Mram) :
      (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) ((eMt0 u).symm F)
  Bu_linL : ∀ u (F : EE), IsLinearMap ℂ (fun φ : Mu u => Bu u φ F)
  Bu_linR : ∀ u (φ : Mu u), IsLinearMap ℂ (fun F : EE => Bu u φ F)
  eMtTw : ∀ u μ, (C.PTw u μ).Mt ≃ₗ[ℂ] Amb μ
  perCol_tie : ∀ u μ, μ ≠ C.mu0 → ∀ (φ : Mu u) (F : Amb μ), perCol u μ φ F =
    (C.PTw u μ).PtilCol (C.e0Tw u μ ((eMu u φ : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ))
      ((eMtTw u μ).symm F)
  eMu_isom : ∀ u (φ ψ : Mu u), inner ℂ φ ψ =
    (C.fm u).ipC 0 ((eMu u φ : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ)
      ((eMu u ψ : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ)

attribute [instance] RowsRest.instEE RowsRest.instEEi RowsRest.instEEf RowsRest.instEE0 RowsRest.instEE0i RowsRest.instEE0f RowsRest.instFT RowsRest.instFTd RowsRest.instAmb RowsRest.instAmbi RowsRest.instAmbf RowsRest.instMult RowsRest.instMulti RowsRest.instMultf RowsRest.instMu RowsRest.instMui RowsRest.instMuf RowsRest.instMj RowsRest.instMji RowsRest.instMjf RowsRest.instMt RowsRest.instMti RowsRest.instMtf RowsRest.instMtL RowsRest.instMtLm

@[reducible] def RowsRest.what₂ {B : Base} {C : Cols B} (W : RowsRest B C) : Rows.Data B.R where
  LL := B.LL
  embLL := B.embLL
  places := B.places
  O := B.O
  OtoLL := B.OtoLL
  Tau := Tau B.R
  card_Tau := card_Tau B.host
  Tup := C.Tup
  mu0 := C.mu0
  muStar := C.muStar
  muStar' := C.muStar'
  Dstar := B.Dstar
  restRowsFiniteGroupCard := B.toPre.restRowsFiniteGroupCard
  restRowsFiniteGroupCard_pos := B.toPre.restRowsFiniteGroupCard_pos
  Word := B.Word
  muAt := W.muAt
  muAt_conj := W.muAt_conj
  muTw := W.muTw
  muTw_conj := W.muTw_conj
  muAt_or := W.muAt_or
  EE := W.EE
  Drows := W.Drows
  onb := W.onb
  Dall := W.Dall
  delp := W.delp
  delp_le_one := W.delp_le_one
  D_eq := W.D_eq
  EE0 := W.EE0
  D0 := W.D0
  onb0 := W.onb0
  FT := W.FT
  ft := W.ft
  ft0 := W.ft0
  Amb := W.Amb
  Mult := W.Mult
  multZero := W.multZero
  multTop := W.multTop
  io := W.io
  Mtilde := W.Mtilde
  eOp := W.eOp
  eOp_idem := W.eOp_idem
  eOp_sa := W.eOp_sa
  Mu := W.Mu
  perCol := W.perCol
  Bu := W.Bu
  ze := W.ze
  rowsRest_wordColumnUnit_baseTuple := W.rowsRest_wordColumnUnit_baseTuple
  Mj := W.Mj
  MjLat := W.MjLat
  kaBig := W.kaBig
  kaSmall := W.kaSmall
  Mt := W.Mt
  MtLat := W.MtLat
  MtL := W.MtL
  jMt := W.jMt
  jMt_basis := W.jMt_basis
  MtLat_sub := W.MtLat_sub
  eMt := W.eMt
  eMt_idem := W.eMt_idem
  eMt_sa := W.eMt_sa
  eMt_LL := W.eMt_LL
  thetaP := W.thetaP
  isot := W.isot
  lamP := W.lamP
  Ij := W.Ij
  jw := W.jw
  etaJ := W.etaJ
  etaJ_nonneg := W.etaJ_nonneg
  shaLen := W.shaLen
  shaLen_nonneg := W.shaLen_nonneg

instance {B : Base} {C : Cols B} (W : RowsRest B C) : NumberField W.what₂.LL := B.nfLL
instance {B : Base} {C : Cols B} (W : RowsRest B C) : StarRing W.what₂.LL := B.starLL

end GlobalTheory.Mem

end
end

section

noncomputable section

namespace GlobalTheory.Mem.ColsModel

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem exists_potential {G A X : Type} [Group G] [CommGroup A] (χ : G →* A) (r : G → X → X → Prop)
    (h1 : ∀ x, r 1 x x) (hi : ∀ g x y, r g x y → r g⁻¹ y x)
    (hm : ∀ g g' x y z, r g x y → r g' y z → r (g' * g) x z) (hs : ∀ g x, r g x x → χ g = 1) :
    ∃ φ : X → A, ∀ g x y, r g x y → (φ x)⁻¹ * φ y = χ g := by
  let s : Setoid X := ⟨fun x y => ∃ g, r g x y, fun x => ⟨1, h1 x⟩, fun ⟨g, h⟩ => ⟨_, hi _ _ _ h⟩,
    fun ⟨g, h⟩ ⟨g', h'⟩ => ⟨_, hm _ _ _ _ _ h h'⟩⟩
  have hb : ∀ x, ∃ g, r g (Quotient.mk s x).out x := fun x => Quotient.mk_out (s := s) x
  choose c hc using hb
  refine ⟨fun x => χ (c x), fun g x y h => ?_⟩
  have e : Quotient.mk s x = Quotient.mk s y := Quotient.sound ⟨g, h⟩
  have h2 := hm _ _ _ _ _ (hm _ _ _ _ _ (hc x) h) (hi _ _ _ (hc y))
  rw [← e] at h2
  have h3 := hs _ _ h2
  simp only [map_mul, map_inv] at h3
  rw [inv_mul_eq_one] at h3
  show (χ (c x))⁻¹ * χ (c y) = χ g
  rw [h3, mul_comm (χ g), inv_mul_cancel_left]

theorem isIntegral_det {E : Type} [Field E] [NumberField E] {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral ℤ γ.det :=
  _root_.GlobalTheory.IsIntegralDetLattice.isIntegral_det_of_preserves_lattice L hfg hsp γ hγ

section Host

variable {R : Ranks} (H : Host R)

def chi : letI := H.cmStar; unitary H.E →* ℂˣ :=
  letI := H.cmStar
  ∏ τ : Tau R, ((Units.map (H.emb ((τ : R.Psi) : R.GG) : H.E →* ℂ)).comp
    Unitary.toUnits)⁻¹

theorem chi_apply : letI := H.cmStar; ∀ z : unitary H.E, ((chi H z : ℂˣ) : ℂ) =
    ∏ τ : Tau R, (H.emb ((τ : R.Psi) : R.GG) (z : H.E))⁻¹ := by
  intro z
  simp [chi]

private theorem prod_sigmaOf (x : H.E) :
    ∏ τ : Tau R, H.sigmaOf ((τ : R.Psi) : R.GG) x = algebraMap H.K H.E (Algebra.norm H.K x) := by
  have := H.galois
  rw [Algebra.norm_eq_prod_automorphisms]
  symm
  have hm : ∀ σ : H.E ≃ₐ[H.K] H.E, H.gal (σ.restrictScalars ℚ) ∈ R.Psi := fun σ =>
    (H.galE_mem_Psi_iff _).2 (σ.commutes ⟨H.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩)
  refine Fintype.prod_bijective (fun σ => ⟨_, hm σ⟩) ⟨fun a b h => ?_, fun τ => ?_⟩ _ _ (fun σ => ?_)
  · exact AlgEquiv.restrictScalars_injective ℚ (H.gal.injective (congrArg Subtype.val h))
  · have h1 : H.sigmaOf τ H.sqd = H.sqd := (H.galE_mem_Psi_iff _).1 (by simpa [Host.sigmaOf] using τ.2)
    have h2 : H.sigmaOf τ ∈ H.K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      induction hy using IntermediateField.adjoin_induction with
      | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact h1
      | algebraMap y => exact AlgEquiv.commutes _ y
      | add y z _ _ hy hz => rw [map_add (f := _), hy, hz]
      | inv y _ hy => rw [map_inv₀, hy]
      | mul y z _ _ hy hz => rw [map_mul, hy, hz]
    refine ⟨IntermediateField.fixingSubgroupEquiv H.K ⟨_, h2⟩, Subtype.ext ?_⟩
    exact H.gal.apply_symm_apply _
  · simp [Host.sigmaOf]

theorem chi_of_integral : letI := H.cmStar; ∀ z : unitary H.E, IsIntegral ℤ (z : H.E) → chi H z = 1 := by
  letI := H.cmStar
  intro z hz
  have := H.isCMField_hostE
  obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one H.E ℂ hz (fun φ => by
    have h1 : star (z : H.E) * z = 1 := z.2.1
    have h2 : φ (star (z : H.E)) = starRingEnd ℂ (φ z) := IsCMField.complexEmbedding_complexConj H.E φ z
    have h3 := congrArg φ h1
    rw [map_mul, h2, map_one, Complex.conj_mul'] at h3
    have h4 : ‖φ z‖ ^ 2 = 1 := by exact_mod_cast h3
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4)
  apply Units.ext
  rw [chi_apply]
  have h := congrArg H.φ₀ (prod_sigmaOf H (z : H.E))
  rw [H.der.norm_mu z ⟨n, hn, hp⟩, map_one, map_one, map_prod] at h
  rw [Finset.prod_inv_distrib, Units.val_one, inv_eq_one]
  exact h

theorem exists_pot (N : ℕ) : letI := H.cmStar; ∃ φ : SDLat H.E N → ℂˣ,
    ∀ (γ : Matrix.unitaryGroup (Fin N) H.E) (L L' : SDLat H.E N),
      L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 →
      (φ L)⁻¹ * φ L' = chi H ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩ := by
  letI := H.cmStar
  let dt : Matrix.unitaryGroup (Fin N) H.E →* unitary H.E :=
    { toFun := fun γ => ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hone : ∀ L : Submodule (𝓞 H.E) (Fin N → H.E), SDLat.smulLat (1 : Matrix (Fin N) (Fin N) H.E) L = L := by
    intro L
    ext v
    simp [SDLat.smulLat]
  have hmul : ∀ (a b : Matrix (Fin N) (Fin N) H.E) (L : Submodule (𝓞 H.E) (Fin N → H.E)),
      SDLat.smulLat (a * b) L = SDLat.smulLat a (SDLat.smulLat b L) := by
    intro a b L
    unfold SDLat.smulLat
    rw [← Submodule.map_comp, Matrix.toLin'_mul]
    rfl
  refine exists_potential ((chi H).comp dt)
    (fun γ (L L' : SDLat H.E N) => L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1)
    (fun L => (hone _).symm) (fun γ L L' h => ?_) (fun γ γ' L L' L'' h h' => ?_) (fun γ L h => ?_)
  · rw [h, ← hmul, ← Submonoid.coe_mul, inv_mul_cancel]
    exact (hone _).symm
  · rw [h', h, ← hmul]; rfl
  · refine chi_of_integral H _ (isIntegral_det L.1 L.2.1 L.2.2.1 _ fun v hv => ?_)
    rw [h]
    exact ⟨v, hv, rfl⟩

end Host

section Chain

open GlobalTheory.MemberTorsor

variable (B : Pre)

def uI : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero


open Classical in
@[reducible] def ch (u : B.Word) : ColumnChain B.R (Tau B.R) (B.hcW u) :=
  haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
  { chain B.R (Tau B.R) (B.hcW u) (B.T u) with
    rhoDet := fun i _ => ((uI⁻¹ * uI ^ (-(((B.R.N (i + 1)) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
    rhoDet' := fun i _ => ((uI * uI ^ ((((B.R.N i) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
    rho_norm := fun _ _ _ => by simp [uI]
    rho'_norm := fun _ _ _ => by simp [uI] }


open Classical in
@[reducible] def member (u : B.Word) : Member B.R (Tau B.R) (B.hcW u) :=
  haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
  { C := ch B u
    A := { atT B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) with
      duStar := B.duStar u, duStar_pos := B.duStar_pos u, Dstar := B.Dstar, Dstar_pos := B.Dstar_pos,
      GamP := B.GamP, one_lt_gammaP := B.one_lt_gammaP }
    P := { period B.R (Tau B.R) (B.hcW u) (B.T u) with } }

@[reducible] def cols0 : Cols0 B where
  mem := member B
  A_T _ := rfl
  A_duStar _ := rfl
  A_Dstar _ := rfl
  A_GamP _ := rfl
  clsLat := letI := B.host.cmStar; fun _ i _ => (B.sp.X i).L0
  clsLat_lat := letI := B.host.cmStar; fun _ i _ => baseLattice_full (B.sp.X i)
  Tup := Fin 3
  mu0 := 0
  muStar := 1
  muStar' := 2
  chTw u _ := ch B u
  memberColumns_twistedChain_base _ := rfl
  e0Tw _ _ := LinearEquiv.refl ℂ _
  PTw u _ := (member B u).P
  Dt := ℂˣ
  detCls _ _ _ := uI
  muTil _ := MonoidHom.id _
  chiD := MonoidHom.id _
  UO := ⊥
  chiD_UO x hx := Subgroup.mem_bot.1 hx
  e1Dt := chi B.host
  rest_detCharacter_on_unitary_eq := chi_apply B.host
  relDet N L L' := QuotientGroup.mk (((exists_pot B.host N).choose L)⁻¹ * (exists_pot B.host N).choose L')
  relDet_self N L := by simp
  relDet_mul N L L' L'' := by
    rw [← QuotientGroup.mk_mul, mul_assoc, mul_inv_cancel_left]
  relDet_smul N L L' γ h := by rw [(exists_pot B.host N).choose_spec γ L L' h]
  rhoDet_eq_inv_muTilde_chiD_pow _ _ _ := rfl
  rhoDetPrime_eq_muTilde_mul_chi_pow _ _ _ := rfl


open Classical in
def cols (B : Base) : Cols B where
  toCols0 := cols0 B.toPre
  fm u :=
    haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
    { forms B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) B.LL B.embLL B.places with }

theorem two_lt_alt (u : B.Word) : 2 < B.T u := by
  have h := B.level_mod_four _ (B.T_level u)
  have h2 := (B.T_prime u).two_le
  omega


end Chain

end GlobalTheory.Mem.ColsModel

end
end
