module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle043
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle034
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle065
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.WeightZeroSectionValueConjPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_archimedean_phaseSpace_coordinates_placeSignatures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∃ (n : ℕ) (θ : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (φ : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ))
      (φ₀ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, GlobalTheory.RealWeil.pPart (φ₀ v) = θ v.1) ∧ (∀ v y, ⟪GlobalTheory.RealWeil.qPart (φ₀ v), θ y⟫ = -GlobalTheory.ArchUniq.trP F κ y v.2) ∧
      (∀ c c', GlobalTheory.RealWeil.sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) ∧
      ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), At (evI F) u →
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          φ c = φ₀ (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) := by
  first | exact @GlobalTheory.ArchCoordsD.exists_coords | exact GlobalTheory.ArchCoordsD.exists_coords | (intros; apply GlobalTheory.ArchCoordsD.exists_coords <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_gaussianVacuum_frames_placeSignatures : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : InfinitePlace F → ℕ}
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (D : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → (SInf F κ →L[ℂ] SInf F κ)),
    IsCMExt F E σ → FramedD τ JA JB a b A C →
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    ∃ f₀ : SInf F κ, f₀ ≠ 0 ∧ ∀ (w : InfinitePlace F) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      At (evI F) u → At (evI F) u' →
      (∀ w', u.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b 1) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      (∀ w', u'.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b Complex.I) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      D u f₀ + (lineSign a b * Complex.I) • D u' f₀ = 0 := by
  first | exact @GlobalTheory.HoweD.exists_vacuumD | exact GlobalTheory.HoweD.exists_vacuumD | (intros; apply GlobalTheory.HoweD.exists_vacuumD <;> assumption)
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.CoverVal

theorem perFr_cast {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X' X : Data E r} (h : SameSp X' X)
    (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X' x v τ i = perFr X (castFr h.psi x) v τ i := by
  obtain ⟨h1, h2, h3, -, -⟩ := h
  cases X
  cases X'
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem sameSp_of {D : D7} {W : HSp D} {r : ℕ} {hr : W.rank = r} {X' X : Data D.host.E r} (h' : IsMod W hr X')
    (h : IsMod W hr X) (hp : X'.p0 = X.p0) : SameSp X' X :=
  ⟨Finset.ext fun τ => (h'.psi τ).trans (h.psi τ).symm, h'.model.1.trans h.model.1.symm, hp,
    h'.model.2.trans h.model.2.symm, h'.kap.trans h.kap.symm⟩

theorem realM_mul {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (γ k : GA D W)
    (δ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (hδ : ∀ (τ : D.host.E →+* ℂ) th, IsInfEmb τ th → archM W th γ = δ.map τ) (τ : D.host.E →+* ℂ)
    (hτ : ∃ ρ, τ = tauE D ρ) :
    realM θ (Formalism.L2.Theta.mt W (γ * k)) τ = δ.map τ * realM θ (Formalism.L2.Theta.mt W k) τ := by
  have h1 := hδ τ (θ hτ.choose) (by have h := hθ hτ.choose; rwa [← hτ.choose_spec] at h)
  rw [realM, realM, dif_pos hτ, dif_pos hτ, ← h1]
  change archM W _ (γ * k) = _ * archM W _ k
  rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]


open CategoryTheory MonObj in
theorem marked_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {L : Lt E r} {y : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) {mk mk' : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : A.Marked mk) (hc : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk' a = mk a + l.M • u) :
    A.Marked mk' := by
  intro a ha
  obtain ⟨u, hu, e'⟩ := hc a ha
  have hM : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := fun u v => by
    unfold pv; rw [per_add]; rfl
  rw [h a ha, e', smul_add, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM, hadd, A.ex_add,
    (A.ex_ker _).2 ⟨u, hu, rfl⟩, _root_.mul_one]

theorem move_congr {A : Type} [CommRing A] {n N : ℕ} (p q : Matrix (Fin n) (Fin n) A) {x x' b w w' : Fin n → A}
    (h : x - q *ᵥ b = N • w) (h' : x' - p *ᵥ (q *ᵥ b) = N • w') : p *ᵥ x - x' = N • (p *ᵥ w - w') := by
  rw [smul_sub, ← h', ← Matrix.mulVec_smul, ← h, Matrix.mulVec_sub, sub_sub_sub_cancel_right]

theorem point_eq {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (h1 : 1 ≤ r) (hA : l.A = 1) {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (hr : W.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (Wt : UW U) (j : U.Comp) (x' : Frame (U.X j).Ψ r) (γ k : GA D W) (hγ : γ ∈ GQ W) (hm' : IsMod W hr (U.X j))
    (hL' : latR hr (latG W (γ * k)) = (U.X j).Λ) (hx' : x' = frMove θ W hr (U.X j) (γ * k) fun τ => x₀ τ.1)
    (hon : IsONFr (U.X j) x') (hk' : MarkAd l W hr ι (γ * k) (Wt.mark j))
    (X : Data D.host.E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (hm : IsMod W hr X) (hp : X.p0 = Dw.q) (hs : IsSympl X bas)
    (hi : IdxIs c σ X idx e) (hL : latR hr (latG W k) = X.Λ) (hmk : IsMark l X.Λ mk) (hk : MarkAd l W hr ι k mk) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ (y : FrPt Xo c ℂ) (A : AnFib X bas idx e (frMove θ W hr X k fun τ => x₀ τ.1) X.Λ y), A.Marked mk →
      ∃ h : x' ∈ (U.X j).dom, y.x = (U.un j ⟨x', h⟩).x := by
  let _ : Algebra c.F ℂ := σ.toAlgebra
  intro y A hA'
  subst hr
  obtain rfl : g = Wt.g := Fin.equiv_iff_eq.1 ⟨e.trans Wt.e.symm⟩
  obtain ⟨π, rfl⟩ : ∃ π : Equiv.Perm (Fin Wt.g), e = π.trans Wt.e :=
    ⟨e.trans Wt.e.symm, Equiv.ext fun a => (Wt.e.apply_symm_apply _).symm⟩
  obtain ⟨idx, rfl⟩ : ∃ idx' : Fin Wt.g ≃ X.Ψ × Fin W.rank, idx = π.trans idx' :=
    ⟨π.symm.trans idx, Equiv.ext fun a => congrArg idx (π.symm_apply_apply a).symm⟩
  have hsp : SameSp (U.X j) X := sameSp_of hm' hm ((hU.2.1 j).1.trans hp.symm)
  obtain ⟨-, hsd, -⟩ := uw_lattice _ H Dw l Xo c σ _ U hσ hU h1 Wt j
  obtain ⟨Dc, hDc, -⟩ := exists_dic _ H Dw l c σ _ Wt.g 0 (U.X j) 0 Wt.e hσ hU.1 (hU.2.1 j).1 (hU.2.1 j).2 hsd
    ⟨fun _ => antitone_const, Even.zero⟩
  have hper := Dc.per_eq
  have hty := Dc.ty_eq
  rw [hDc] at hper hty
  obtain ⟨hd', hu', -⟩ := hx_of_isONFr _ _ _ 0 (U.X j) Dc.bas Dc.idx Dc.sympl Even.zero x' hon
  obtain ⟨A', hA'', -⟩ := uw_anFib _ H Dw l Xo c σ _ U hσ hU h1 Wt j Dc.bas Dc.idx Dc.sympl hper hty ⟨x', hd'⟩ hu'
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix W γ hγ
  have hri : ∀ v, δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, (δ⁻¹).1 *ᵥ (δ.1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hG : X.Gm = -W.gram.transpose := hm.model.1
  have hun : IsUn X δ⁻¹ := fun u v => by rw [hG, ← hδu, hri, hri]
  have hR : ∀ L : Lt D.host.E W.rank, latR rfl L = L := fun L => Submodule.map_id L
  rw [hR] at hL hL'
  have hmem : ∀ v, v ∈ X.Λ ↔ δ.1 *ᵥ v ∈ (U.X j).Λ := fun v => by
    rw [← hL, ← hL', GlobalTheory.Member.LatMove.mem_lat_iff, GlobalTheory.Member.LatMove.mem_lat_iff,
      GlobalTheory.Member.LatMove.move_iff W γ k, hδf]
  obtain ⟨hd, -, hsd', A'', -, -, hM⟩ := anFib_move _ H Dw l Xo c _ _ (U.X j) X hsp Dc.bas Dc.idx bas idx Wt.e x' _ _ A' δ⁻¹
    Dc.sympl hs hd' hsd hun
    (fun v => funext fun a => by
      obtain ⟨a, rfl⟩ := π.surjective a
      exact (hper x' v _).trans ((perFr_cast hsp _ _ _ _).trans (hi.1 _ v a).symm))
    (fun a => by
      obtain ⟨a, rfl⟩ := π.surjective a
      exact (hty _).trans (hi.2 a).symm)
  have hM' := hM _ hA''
  have e1 : mapL δ⁻¹ (U.X j).Λ = X.Λ := Submodule.ext fun v => by
    rw [Lev.mem_mapL, inv_inv, hmem]; rfl
  have e2 : lact δ⁻¹ (castFr hsp.psi x') = frMove θ W rfl X k fun τ => x₀ τ.1 := by
    funext τ
    rw [hx']
    change (δ⁻¹).1.map τ.1 * (realM θ (Formalism.L2.Theta.mt W (γ * k)) τ.1 * x₀ τ.1) =
      realM θ (Formalism.L2.Theta.mt W k) τ.1 * x₀ τ.1
    rw [realM_mul hθ W γ k δ.1 hδa τ.1 ((hm.psi _).1 τ.2), ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul,
      Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  revert A'' hd hsd'
  rw [e1, e2]
  intro hd hsd' A'' _ hM'
  refine ⟨hd', anFib_point_eq _ H Dw l Xo c hA _ _ X bas idx Wt.e _ _ _ y A'' (Cmp.anFibRen π A) hs hd hsd' mk hmk
    (marked_congr A'' hM' fun a ha => ?_) hA'⟩
  obtain ⟨w, hw, ew⟩ := hk a ha
  obtain ⟨w', hw', ew'⟩ := hk' a ha
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨u, hu, eu⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0 (δ.1 *ᵥ mk a - Wt.mark j a) ((finHom W γ).1 *ᵥ w - w') (by
    have e3 : finVec W (δ.1 *ᵥ mk a - Wt.mark j a) = finVec W (δ.1 *ᵥ mk a) - finVec W (Wt.mark j a) :=
      funext fun i => TensorProduct.tmul_sub _ _ _
    rw [e3, ← hδf]
    exact move_congr _ _ ew (GlobalTheory.Member.LatMove.fin_mul W γ k _ ▸ ew'))
  refine ⟨(δ⁻¹).1 *ᵥ u, ?_, ?_⟩
  · rw [hmem, hri, ← hL', GlobalTheory.Member.LatMove.mem_lat_iff, hu]
    exact sub_mem (GlobalTheory.Member.LatMove.move_mem W γ k w hw) hw'
  · rw [← Matrix.mulVec_smul, ← eu, Matrix.mulVec_sub, hli]
    exact (add_sub_cancel _ _).symm

theorem evR_eq_of_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (σ : c.F →+* ℂ) {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    (y y' : FrPt Xo c (CAt σ)) (h : y'.x = y.x) : toC (evR Xo c f y') = toC (evR Xo c f y) :=
  GlobalTheory.WeightZeroValue.evR_conj E H Dw l Xo c σ (RingEquiv.refl ℂ) f hf y y'
    (h.trans ((CategoryTheory.Category.id_comp _).symm.trans
      (congrArg (CategoryTheory.CategoryStruct.comp · y.x) (AlgebraicGeometry.Spec.map_id _).symm)))

end GlobalTheory.AdTh.CoverVal
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem exists_crd_of_mem_unipRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ u ∈ unipRad σ J C, ∃ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c ∧ c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0 := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF u hu
  obtain ⟨hC, b, hZ⟩ := (mem_unipRad_iff_frame F E σ n J j m C D Z J₀ hF u).1 hu
  set s := sigR (AF F) σ with hsdef
  set M := (matHom _ σ J u).1 with hMdef
  have hU : cT s M * adMat F J * M = adMat F J := u.2
  have hs : ∀ a : AF F ⊗[F] E, s (s a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma hF.cm x)
  have cc : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)), cT s (cT s X) = X :=
    fun X => Matrix.ext fun i k => hs _
  have cadd : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)), cT s (X + Y) = cT s X + cT s Y :=
    fun X Y => Matrix.ext fun i k => map_add s _ _
  have csub : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)), cT s (X - Y) = cT s X - cT s Y :=
    fun X Y => Matrix.ext fun i k => map_sub s _ _
  have cad : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) E), cT s (adMat F X) = adMat F (cT (σ : E →+* E) X) :=
    fun X => GlobalTheory.AutFunCounterexample.cT_map_gen σ X
  have gram : ∀ {a b : ℕ} (X : Matrix (Fin n) (Fin a) E) (Y : Matrix (Fin n) (Fin b) E),
      cT s (adMat F X) * adMat F J * adMat F Y = adMat F (cT (σ : E →+* E) X * J * Y) := fun X Y => by
    rw [cad]; simp only [adMat, Matrix.map_mul]
  have unit : ∀ {a b : ℕ} (X : Matrix (Fin n) (Fin a) (AF F ⊗[F] E)) (Y : Matrix (Fin n) (Fin b) (AF F ⊗[F] E)),
      cT s (M * X) * adMat F J * (M * Y) = cT s X * adMat F J * Y := fun X Y => by
    have e : cT s X * cT s M * adMat F J * (M * Y) = cT s X * (cT s M * adMat F J * M) * Y := by
      simp only [Matrix.mul_assoc]
    rw [Formalism.UG.cT_mul, e, hU]
  have ad0 : ∀ {a b : ℕ}, adMat F (0 : Matrix (Fin a) (Fin b) E) = 0 := fun {a b} => Matrix.map_zero _ (map_zero _)
  have ad1 : ∀ {a : ℕ}, adMat F (1 : Matrix (Fin a) (Fin a) E) = 1 := fun {a} => Matrix.map_one _ (map_zero _) (map_one _)

  have h1 : cT s (adMat F C) * adMat F J * (M * adMat F D) = 1 := by
    conv_lhs => rw [← hC]
    rw [unit, gram, hF.cd, ad1]
  have h2 : cT s (adMat F Z) * adMat F J * (M * adMat F D) = - cT s b := by
    have e := unit (adMat F Z) (adMat F D)
    rw [hZ, gram, hF.zd, ad0, cadd, Formalism.UG.cT_mul, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc (cT s b),
      Matrix.mul_assoc (cT s b), h1, Matrix.mul_one] at e
    exact eq_neg_of_add_eq_zero_left e
  set c := cT s (adMat F D) * adMat F J * (M * adMat F D) with hc
  have hsum : adMat F C * (cT s (adMat F D) * adMat F J) + adMat F Z * (adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J)) +
      adMat F D * (cT s (adMat F C) * adMat F J) = 1 := by
    have e := congrArg (fun X => adMat F X) hF.sum
    simp only [adMat, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at e
    simp only [cad, adMat]
    exact e
  have hD : M * adMat F D = adMat F D - adMat F Z * plus σ J₀ b + adMat F C * c := by
    conv_lhs => rw [← Matrix.one_mul (M * adMat F D), ← hsum]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (cT s (adMat F D)), ← Matrix.mul_assoc (cT s (adMat F Z)),
      ← Matrix.mul_assoc (cT s (adMat F C)), h1, h2, Matrix.mul_one, plus, Matrix.mul_neg, Matrix.mul_neg, ← hc]
    abel
  refine ⟨b, c, ⟨hC, hZ, hD⟩, ?_⟩

  have h0 := unit (adMat F D) (adMat F D)
  rw [gram, hF.dd, ad0] at h0
  have hP : cT s (plus σ J₀ b) = b * adMat F J₀⁻¹ := by
    rw [plus, Formalism.UG.cT_mul, cc, cad, GlobalTheory.UAut.cT_form_inv hF.herm₀]
  conv_lhs at h0 => rw [hD]
  rw [cadd, csub, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hP, Matrix.add_mul, Matrix.sub_mul, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_assoc (b * adMat F J₀⁻¹), Matrix.mul_assoc (b * adMat F J₀⁻¹), Matrix.mul_assoc (cT s c),
    Matrix.mul_assoc (cT s c), ← hD, h1, h2, ← hc, Matrix.mul_one] at h0
  rw [← h0, plus, Matrix.mul_neg, Matrix.mul_assoc]
  abel

end GlobalTheory.SphEis
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.reduction_leviGL_isotropicFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∃ (W : Set (GAd σ J)) (B : ℝ), IsCompact W ∧ ∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∃ γ ∈ ratPts σ J, γ ∈ parFlag σ J C (fun _ => 0) ∧ ∃ q ∈ fixG σ J C, ∃ l : Fin j → ℤ, ∃ w ∈ W, γ * p = q * lv (tor F E l) * w ∧ (absE F E (Matrix.GeneralLinearGroup.det β) : ℝ) ≤ B * ∏ i, (bse F ^ l i)⁻¹ := by
  first | exact @GlobalTheory.SphEis.reduce_levi | exact GlobalTheory.SphEis.reduce_levi | (intros; apply GlobalTheory.SphEis.reduce_levi <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem lv_comm_of_fix_cols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ α, ∀ x ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), lv α * x = x * lv α := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv α x hx
  obtain ⟨hxC, hxD⟩ := Subgroup.mem_inf.mp hx
  have hC : (matHom _ σ J x).1 * adMat F C = adMat F C := hxC
  have hD : (matHom _ σ J x).1 * adMat F D = adMat F D := hxD
  have formOf : ∀ (K : Matrix (Fin n) (Fin j) E), x⁻¹ ∈ fixG σ J K →
      adMat F (cT (σ : E →+* E) K * J) * (matHom _ σ J x).1 = adMat F (cT (σ : E →+* E) K * J) := by
    intro K hK
    have h1 : (matHom _ σ J x⁻¹).1 * adMat F K = adMat F K * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]; exact hK
    have := form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at this
  have fC := formOf C ((fixG σ J C).inv_mem hxC)
  have fD := formOf D ((fixG σ J D).inv_mem hxD)
  set X := (matHom _ σ J x).1 with hX
  have hZ : X * adMat F Z = adMat F Z * (adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * X * adMat F Z) := by
    have h1 : adMat F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    have e : X * adMat F Z = adMat F (C * (cT (σ : E →+* E) D * J) +
        Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + D * (cT (σ : E →+* E) C * J)) * X * adMat F Z := by
      rw [hF.sum, h1, Matrix.one_mul]
    have z1 : adMat F (cT (σ : E →+* E) D * J) * X * adMat F Z = 0 := by
      rw [fD, adMat, adMat, ← Matrix.map_mul, hF.dz, Matrix.map_zero _ (map_zero _)]
    have z2 : adMat F (cT (σ : E →+* E) C * J) * X * adMat F Z = 0 := by
      rw [fC, adMat, adMat, ← Matrix.map_mul, hF.cz, Matrix.map_zero _ (map_zero _)]
    have hadd : ∀ {p : ℕ} (A B : Matrix (Fin n) (Fin p) E), adMat F (A + B) = adMat F A + adMat F B :=
      fun A B => Matrix.map_add _ (map_add _) A B
    have hmul : ∀ {p : ℕ} (A : Matrix (Fin n) (Fin p) E) (B : Matrix (Fin p) (Fin n) E),
        adMat F (A * B) = adMat F A * adMat F B := fun A B => Matrix.map_mul
    rw [e, hadd, hadd, hmul, hmul, hmul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul,
      Matrix.mul_assoc (adMat F C), Matrix.mul_assoc (adMat F C), z1, Matrix.mul_assoc (adMat F D),
      Matrix.mul_assoc (adMat F D), z2, Matrix.mul_zero, Matrix.mul_zero, zero_add, add_zero,
      Matrix.mul_assoc (adMat F Z), Matrix.mul_assoc (adMat F Z)]
  apply eq_of_frame_cols F E σ n J j m C D Z J₀ hF
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hlv.onC, ← hX, hC,
      ← Matrix.mul_assoc, hC, hlv.onC]
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hlv.onZ, ← hX, hZ,
      ← Matrix.mul_assoc, hlv.onZ]
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hlv.onD, ← hX, hD,
      ← Matrix.mul_assoc, hD, hlv.onD]

end GlobalTheory.SphEis
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem aemeasurable_fibDens {ι : Type} [Fintype ι] {m : ι → ℕ} {d : ℕ} (G : V d → Mat m ℂ) (O : Set (V d))
    (hO : IsOpen O) (hG : ∀ τ i j, ContinuousOn (fun v => G v τ i j) O) :
    AEMeasurable (fun x : V d × (Cell m → ℂ) => fibDens (G x.1) x.2)
      (volume.restrict (O ×ˢ (Set.univ : Set (Cell m → ℂ)))) := by
  have hS : MeasurableSet (O ×ˢ (Set.univ : Set (Cell m → ℂ))) := hO.measurableSet.prod MeasurableSet.univ
  have hGτ : ∀ τ, ContinuousOn (fun x : V d × (Cell m → ℂ) => G x.1 τ) (O ×ˢ Set.univ) := by
    intro τ
    have h : ContinuousOn (fun v => G v τ) O :=
      continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hG τ i j
    exact h.comp continuous_fst.continuousOn fun x hx => hx.1
  unfold fibDens
  apply Finset.aemeasurable_fun_prod
  intro τ _
  refine AEMeasurable.mul (AEMeasurable.mul aemeasurable_const ?_) ?_
  · have h := ((continuous_id.matrix_det).comp_continuousOn (hGτ τ))
    exact ((Complex.continuous_re.comp_continuousOn h).aemeasurable hS).pow_const _
  · unfold GlobalTheory.FlagFibre.dens
    apply Finset.aemeasurable_fun_prod
    intro i _
    refine AEMeasurable.pow_const (AEMeasurable.norm ?_) _
    have hc : Continuous fun p : Matrix (Fin (m τ)) (Fin (m τ)) ℂ × (Low (m τ) → ℂ) =>
        ReciprocityTheory.ChartRestriction.G.FD.lminor ((GlobalTheory.FlagFibre.uni p.2)ᴴ * p.1ᵀ * GlobalTheory.FlagFibre.uni p.2) i.castSucc := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.lminor
      exact ((((GlobalTheory.FlagFibre.continuous_uni.comp continuous_snd).matrix_conjTranspose.matrix_mul
        continuous_fst.matrix_transpose).matrix_mul (GlobalTheory.FlagFibre.continuous_uni.comp continuous_snd)).matrix_submatrix
        _ _).matrix_det
    have h2 : ContinuousOn (fun x : V d × (Cell m → ℂ) => (G x.1 τ, fun s => x.2 ⟨τ, s⟩)) (O ×ˢ Set.univ) :=
      (hGτ τ).prodMk (by fun_prop : Continuous fun x : V d × (Cell m → ℂ) => fun s => x.2 ⟨τ, s⟩).continuousOn
    exact (hc.comp_continuousOn h2).aemeasurable hS

end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem setLIntegral_fibDens : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (δ : V d → ℝ) (O K : Set (V d)), IsOpen O → MeasurableSet K → K ⊆ O → ContinuousOn δ O → (∀ τ i j, ContinuousOn (fun v => G v τ i j) O) → (∀ v ∈ O, ∀ τ, (G v τ).PosDef) → ∫⁻ w in bsL ε ⁻¹' K, ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w)) = ∫⁻ v in K, ENNReal.ofReal (δ v) := by
  intro ι _ m n d ε G δ O K hO hK hKO hδ hG hpos
  have hmp := (GlobalTheory.FlagCell2.measurePreserving_pt_split n d (Cell m) ε).1
  have hb : Measurable (bsL ε) := (bsL ε).continuous.measurable
  have hm := hmp.restrict_preimage (hb hK)
  have hs : (fun x : V d × (Cell m → ℂ) => pt ε x.1 x.2) ⁻¹' (bsL ε ⁻¹' K) = K ×ˢ Set.univ := by
    ext x
    simp [bsL_pt]
  rw [hs, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at hm
  set F : V d × (Cell m → ℂ) → ℝ≥0∞ := fun x => ENNReal.ofReal (δ x.1 * fibDens (G x.1) x.2) with hF
  have hS : MeasurableSet (O ×ˢ (Set.univ : Set (Cell m → ℂ))) := hO.measurableSet.prod MeasurableSet.univ
  have hFO : AEMeasurable F (volume.restrict (O ×ˢ (Set.univ : Set (Cell m → ℂ)))) := by
    refine ENNReal.measurable_ofReal.comp_aemeasurable (AEMeasurable.mul ?_ (aemeasurable_fibDens G O hO hG))
    exact (hδ.comp continuous_fst.continuousOn (fun x (hx : x ∈ O ×ˢ (Set.univ : Set (Cell m → ℂ))) => hx.1)).aemeasurable hS
  have hFK : AEMeasurable F ((volume.restrict K).prod volume) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure (Cell m → ℂ))), Measure.prod_restrict,
      ← Measure.volume_eq_prod]
    exact hFO.mono_measure (Measure.restrict_mono (Set.prod_mono hKO subset_rfl) le_rfl)
  have e1 : (fun w => ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w))) ∘
      (fun x : V d × (Cell m → ℂ) => pt ε x.1 x.2) = F := by
    funext x
    simp [hF, bsL_pt, fb_pt]
  have hH : AEMeasurable (fun w => ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w)))
      (Measure.map (fun x : V d × (Cell m → ℂ) => pt ε x.1 x.2) ((volume.restrict K).prod volume)) := by
    rw [(GlobalTheory.FlagCell2.measurePreserving_pt_split n d (Cell m) ε).2.aemeasurable_map_iff, e1]
    exact hFK
  rw [← hm.map_eq, lintegral_map' hH hm.measurable.aemeasurable]
  refine (lintegral_congr fun a => congrFun e1 a).trans ?_
  rw [lintegral_prod _ hFK]
  refine setLIntegral_congr_fun hK fun v hv => ?_
  obtain ⟨h0, h1⟩ := GlobalTheory.FlagCell2.fibDens_mass ι m (G v) (hpos v (hKO hv))
  simp only [hF]
  simp_rw [ENNReal.ofReal_mul' (h0 _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h1, mul_one]

end GlobalTheory.FlagCell2
end

section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

theorem _root_.GlobalTheory.T.free_action_framedPoints_of_unipotent_mod_two_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (G : Type) [Group G] (h : G → (Dw.La →ₗ[𝓞 E] Dw.La)) (m g₁ g₂ : ℕ) (I₁ I₂ : Ideal (𝓞 E)), 1 ≤ Dw.p + Dw.q → g₁.Prime → g₂.Prime → g₁ ≠ g₂ → I₁ ≠ ⊤ → I₂ ≠ ⊤ → (g₁ : 𝓞 E) ∈ I₁ → (g₂ : 𝓞 E) ∈ I₂ → l.Mb ≤ I₁ → l.Mb ≤ I₂ → (∀ g x, ((h g - 1) ^ m) x ∈ I₁ • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ g x, ((h g - 1) ^ m) x ∈ I₂ • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ g, (∀ x, h g x - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → g = 1) → FreePt Xo c (fun g => (h g, (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La))) := by
  first | exact @GlobalTheory.FreeLev.free_of_unip | exact GlobalTheory.FreeLev.free_of_unip | (intros; apply GlobalTheory.FreeLev.free_of_unip <;> assumption)
end
