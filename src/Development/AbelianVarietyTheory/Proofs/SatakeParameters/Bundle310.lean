module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DeterminantCharacterUnitaryApply
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle073
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle168
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle300
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwLatRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem seam_lat_gmap {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (N : Submodule (𝓞 X.E) (Sp X.E n)) : s.lat (Formalism.HermitianLatticesTheory.gmap g N) = mvL (seamGL s g) (s.lat N) := by
  ext y
  rw [s.mem_lat]
  unfold mvL
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Formalism.L2.Col.mem_gmap] at hx
    refine ⟨s.vec (g.symm x), (s.mem_lat N _).2 ⟨_, hx, rfl⟩, ?_⟩
    show (seamGL s g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ (fun l => s.iE (g.symm x l)) = fun l => s.iE (x l)
    rw [seamGL_mulVec, LinearEquiv.apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := (s.mem_lat N w).1 hw
    refine ⟨g x0, ?_, ?_⟩
    · rw [Formalism.L2.Col.mem_gmap, LinearEquiv.symm_apply_apply]; exact hx0
    · show (fun l => s.iE (g x0 l)) = (seamGL s g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ (fun l => s.iE (x0 l))
      rw [seamGL_mulVec]



theorem lat_moved : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → t.seam.lat ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1.N = latCo D.sp (gramN D i hi) (A.crd i hi) a x₁.1 ((St i hi).K β).lev.Lb) := by
  intro D _ _ _ _ _ _ _ _ t u μ St A dtU a _ _ i hi β x x₁ γ hγ hx g hg p hp
  have e1 : ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1.N = Formalism.HermitianLatticesTheory.gmap g.1 p.deco.1.N := rfl
  rw [e1, seam_lat_gmap, hg, hp.lat, hx, latCo_rat _ _ _ hγ]

end GlobalTheory.TwLatRat

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem chi_detId_lat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => (∀ (N : ℕ) (M M' : SDLat D.host.E N), ∀ g ∈ Formalism.L2.Herm.UstdAf D.sp.cm N, Formalism.L2.Herm.Carries g M.1 M'.1 → ∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Formalism.L2.Herm.IsDetOf D.sp.cm y g → D.relDet N M M' = QuotientGroup.mk (dtU y)) → (∀ i hi β, latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb = StandardLatticesGL3.stdL D (D.R.N i)) → ∀ i (hi : i ≤ D.R.m) c, t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (t.seam.lat ((t.rd u μ).N i c))) = ((D.chiD ((t.O u μ).dt i c) : ℂˣ) : ℂ)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ _ _ i hi c
  rw [← t.O_lat, t.χ_rec, ← Formalism.L2.Ker.initial_lattice_eq_standard (t.O u μ) i, ← t.idl_ok.2.2.2.2 _ ((t.O u μ).L0 i) ((t.O u μ).lat i c),
    ← (t.O u μ).dt_lat, TaylorLogMetric.chiRec_idl D t.idl t.idl_ok.1]
  rfl

end GlobalTheory.TwV
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem inFr_inFr_eq_toLin {E : Type} [Field E] {a b : ℕ} (f g : Sp E a ≃ₗ[E] Sp E a) (f' g' : Sp E b ≃ₗ[E] Sp E b)
    (N : Matrix (Fin b) (Fin b) E) (hN : LinearMap.toMatrix' (f'.trans g').toLinearMap * N = 1) (z : HomE E a b) :
    inFr f f' (inFr g g' z) = Matrix.toLin' N ∘ₗ z ∘ₗ Matrix.toLin' (LinearMap.toMatrix' (f.trans g).toLinearMap) := by
  rw [Matrix.toLin'_toMatrix']
  have key : ∀ y, Matrix.toLin' N y = (f'.trans g').symm y := by
    intro y
    have h : (f'.trans g') (Matrix.toLin' N y) = y := by
      have h0 := congrArg (fun M => Matrix.toLin' M y) hN
      rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix'] at h0
      exact h0
    exact ((f'.trans g').symm_apply_eq.2 h.symm).symm
  ext w l
  simp only [inFr, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, key, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply]


theorem adelicDatum_at_translates : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)), ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), ∀ (κ : ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.U) (κ' : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U), x.1 = ratA D.host.F γ * ((St i (Nat.le_of_succ_le hi)).y c).1 * κ.1 → x'.1 = ratA D.host.F γ' * ((St (i + 1) hi).y c').1 * κ'.1 → (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) * star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) = 1 → ∀ z, muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.chi κ : ℂˣ) : ℂ) * Xi i hi ((St i (Nat.le_of_succ_le hi)).chOf c) ((St (i + 1) hi).chOf c') x x' z = muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.chi κ' : ℂˣ) : ℂ) * (t.rd u μ).Xi i c c' (seamHom t.seam (Matrix.toLin' (star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap)) ∘ₗ z ∘ₗ Matrix.toLin' (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi))).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)).toLinearMap)))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ Xi muT law i hi c c' x x' γ hγ γ' hγ' κ κ' hx hx' hM z
  have hr : ratA D.host.F γ ∈ UPts (sigD D) (gramN D i (Nat.le_of_succ_le hi)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Formalism.UG.P.rational_points_le_holds _ _ _ _ _ _ ⟨γ, hγ, rfl⟩
  have hr' : ratA D.host.F γ' ∈ UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Formalism.UG.P.rational_points_le_holds _ _ _ _ _ _ ⟨γ', hγ', rfl⟩
  let x₀ : UA D i (Nat.le_of_succ_le hi) := ⟨ratA D.host.F γ * ((St i _).y c).1, mul_mem hr ((St i _).y c).2⟩
  let x₀' : UA D (i + 1) hi := ⟨ratA D.host.F γ' * ((St (i + 1) hi).y c').1, mul_mem hr' ((St (i + 1) hi).y c').2⟩
  have h1 := law.lev i hi ((St i _).chOf c) ((St (i + 1) hi).chOf c') x₀ x₀' x x' κ κ' hx hx' z
  have h2 := law.rat i hi ((St i _).chOf c) ((St (i + 1) hi).chOf c') ((St i _).y c) ((St (i + 1) hi).y c') x₀ x₀' γ hγ γ' hγ' rfl rfl z
  have h3 := law.read i hi c c' (inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)
  refine h1.trans ?_
  rw [h2, h3, inFr_inFr_eq_toLin _ _ _ _ _ hM z]

end GlobalTheory.TwV
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

open Matrix

section Gen

variable {E : Type} [Field E] {N : ℕ}

theorem unit_hform_mulVec (σ : E →+* E) (J B : Matrix (Fin N) (Fin N) E) (x y : Fin N → E) :
    hform σ J (B *ᵥ x) (B *ᵥ y) = hform σ (cT σ B * J * B) x y := by
  have key : ∀ (K : Matrix (Fin N) (Fin N) E) (v w : Fin N → E), hform σ K v w = (σ ∘ v) ⬝ᵥ (K *ᵥ w) := by
    intro K v w
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h1 : σ ∘ (B *ᵥ x) = (B.map σ) *ᵥ (σ ∘ x) := funext fun l => RingHom.map_mulVec σ B x l
  rw [key, key, h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (σ ∘ x), cT,
    Matrix.vecMul_transpose]

theorem unit_hform_one (σ : E →+* E) (x y : Fin N → E) : hform σ 1 x y = ∑ a, σ (x a) * y a := by
  simp [hform, Matrix.one_apply]

theorem cT_mul_self_of_hform (σ : E →+* E) (M : Matrix (Fin N) (Fin N) E)
    (h : ∀ x y, hform σ 1 (M *ᵥ x) (M *ᵥ y) = hform σ 1 x y) : cT σ M * M = 1 := by
  ext p q
  have h1 := h (Pi.single p 1) (Pi.single q 1)
  rw [unit_hform_mulVec, Matrix.mul_one] at h1
  simpa [hform, Pi.single_apply, apply_ite σ] using h1

end Gen

section Gen2

variable {E : Type} [Field E] {N : ℕ}

theorem cT_mul_self_toStdCo_stdG (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E)
    (hco : cT σ co.1 * co.1 = J) (hγ : γ ∈ UJ σ J) :
    cT σ (LinearMap.toMatrix' ((toStdCo σ J co).trans (stdG σ J γ)).toLinearMap) *
      LinearMap.toMatrix' ((toStdCo σ J co).trans (stdG σ J γ)).toLinearMap = 1 := by
  have hc : IsOrthCo σ J (toLE co) := by
    intro x y
    have h := unit_hform_mulVec σ 1 co.1 x y
    rw [Matrix.mul_one, hco, unit_hform_one] at h
    exact h
  have hs : IsOrthCo σ J (stdCo σ J) := Classical.epsilon_spec (p := IsOrthCo σ J) ⟨_, hc⟩
  have hγ' : cT σ γ.1 * J * γ.1 = J := hγ
  apply cT_mul_self_of_hform
  intro x y
  rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, unit_hform_one, unit_hform_one]
  obtain ⟨x, rfl⟩ := (toLE co).surjective x
  obtain ⟨y, rfl⟩ := (toLE co).surjective y
  rw [hc]
  simp only [toStdCo, stdG, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [hs]
  have h := unit_hform_mulVec σ J γ.1 x y
  rw [hγ'] at h
  exact h

end Gen2

theorem ratIsometry_unitary : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) * star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _ i hi γ hγ
  have h := cT_mul_self_toStdCo_stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi) γ (hP.crd_orth i hi) hγ
  rw [mul_eq_one_comm] at h
  exact h

end GlobalTheory.TwV

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem levSrc_localData : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 < D.R.m) (β : (St t.m2 hi.le).Ch) (κ : ((St t.m2 hi.le).K β).lev.U),
    ∃ (g : SB t μ → (Sp t.X.E (D.R.N t.m2) ≃ₗ[t.X.E] Sp t.X.E (D.R.N t.m2))) (z : SB t μ → t.X.K),
      (∀ P, A.midRel t.m2 hi β P (g P) (z P) ∧ InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 (g P)) ∧
      ((((St t.m2 hi.le).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (∏ P, z P) = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie hi β κ
  obtain ⟨hLe, -, hChi⟩ := hTie.levMid t.m2 hi le_rfl β
  have hκ := (((St t.m2 hi.le).K β).lev.U_eq κ.1).1 κ.2
  have key : ∀ P : SB t μ, ∃ g z, A.midRel t.m2 hi β P g z ∧
      InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 g := by
    intro P
    refine hLe P (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) ?_ κ.1 hκ.1 (hκ.2 _)
    unfold IsOver
    rw [HeightOneSpectrum.under_asIdeal]
  choose g z hgz using key
  exact ⟨g, z, hgz, hChi κ g z hgz⟩

end GlobalTheory.TwV
end
end

section

noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem smul_sub_mem_of_frames {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))}
    {N : Submodule (𝓞 E) (Sp E n)} {fr : Frs E n SB} (hf : GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.IsFrames N fr) (P : SB) (s : E) (a b y₀ : Sp E n)
    (ha : ∀ l, IntAt P.1 (s * ((fr P).symm a - y₀) l)) (hb : ∀ l, IntAt P.1 (s * ((fr P).symm b - y₀) l)) :
    s • (a - b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal N := by
  have h : s • (fr P).symm (a - b) ∈ stdAt E n P.1 := GlobalTheory.TopStep.mem_stdAt.2 fun l => by
    have := GlobalTheory.TopStep.intAt_sub (ha l) (hb l)
    convert this using 1
    simp only [Pi.smul_apply, smul_eq_mul, map_sub, Pi.sub_apply]
    ring
  have := (hf P _).2 h
  rwa [map_smul, LinearEquiv.apply_symm_apply] at this

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}

theorem chartBaseRepresentative_penultimate_step (A : AdData t u μ St) (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ) :
    y0At A (t.m2 + 1) hi β P = A.y0 β P := by
  unfold y0At
  rw [dite_eq_left rfl]

end

theorem cosetOf_eq_yb : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ c, cosetOf A (t.m2 + 1) (cpl_lt t μ).le ((St _ (cpl_lt t μ).le).chOf c) (A.pt _ (cpl_lt t μ).le c) = A.yb c) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ H c
  obtain ⟨w, -, hw⟩ := H.chain.2.1 c
  have hwm : w ∈ A.yb c := by
    rw [hw, Set.mem_setOf_eq, sub_self]
    exact zero_mem _
  ext y
  constructor
  · intro hy
    rw [hw, Set.mem_setOf_eq, locLat, Submodule.mem_iInf]
    intro P
    rw [Submodule.mem_comap]
    have h1 := hy P
    have h2 := H.coset c w hwm P
    rw [chartBaseRepresentative_penultimate_step] at h1
    unfold SameCoset at h1 h2
    have key := smul_sub_mem_of_frames (GlobalTheory.ColPeriod.isFrames_frsF (A.pt _ (cpl_lt t μ).le c)) P _ y w _ h1 h2
    by_cases hP : P.1 ∈ t.Pr.vGs
    · simp only [hP, if_true] at key ⊢
      simpa using key
    · simp only [hP, if_false] at key ⊢
      simpa [zpow_natCast] using key
  · intro hy P
    rw [chartBaseRepresentative_penultimate_step]
    exact H.coset c y hy P

end GlobalTheory.TwV

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem mt_ratId : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨i, hi⟩) ∧ ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 → ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 = ratId D.host.F D.host.E z → (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _ i hi
  choose e he using fun τ => (D.hc τ).e_int ⟨i, hi⟩
  refine ⟨e, fun τ => (he τ).symm, fun z hz y hy => ?_⟩
  have hstar : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have hz' : (z : D.host.E) ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, hstar]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  obtain ⟨k, hk⟩ := GlobalTheory.Mem.Col2.exists_eq_div_conj D.host ⟨z, hz'⟩
  simp only at hk
  let k' : t.X.Eˣ := Units.map t.seam.iE.symm.toRingHom.toMonoidHom k
  have hik : t.seam.iE (k' : t.X.E) = k := t.seam.iE.apply_symm_apply _
  have hq : A.q (ratId t.X.F t.X.E k') = dtU y := by
    apply hP.q_dt
    rw [hy]
    have hx : Units.map A.iA.toRingHom.toMonoidHom (ratId t.X.F t.X.E k') = ratId D.host.F D.host.E k := by
      apply Units.ext
      show A.iA ((k' : t.X.E) ⊗ₜ[t.X.F] 1) = (k : D.host.E) ⊗ₜ[D.host.F] 1
      rw [hP.iA_rat, hik]
    rw [hx, h90, MonoidHom.div_apply, MonoidHom.id_apply, eq_div_iff_mul_eq']
    apply Units.ext
    show ((z : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) *
      (Formalism.UG.sigR (Formalism.L2.Forms.sigD D) _ ((k : D.host.E) ⊗ₜ[D.host.F] 1)) = (k : D.host.E) ⊗ₜ[D.host.F] 1
    rw [Formalism.UG.sigR]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have hs : Formalism.L2.Forms.sigD D (k : D.host.E) = D.host.conj k := bridge_star_holds D.R D.host _
    rw [hs, hk]
  have hmu : ((D.muTil (i + 1) (A.q (ratId t.X.F t.X.E k')) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ := by
    obtain ⟨ι, hι⟩ := exists_isAdIso t.X.F t.X.E
    rw [hP.muTil ι hι ⟨i, hi⟩ (GlobalTheory.Mem.Chr.finPartI _ (Neutral.B1.diagUnits _ k')) _ (GlobalTheory.KerJ.RatPts.isFin_finPart _)
      ((hι.1 (k' : t.X.E)).trans rfl), GlobalTheory.Mem.Chr.DetGroupModel.fin_diag, Units.val_inv_eq_inv_val]
    obtain ⟨n, hn, hinf⟩ := (hP.mu0 ⟨i, hi⟩).inf
    rw [hinf k', ← Finset.prod_inv_distrib, ← t.seam.iT.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hme : n τ = 2 * -e (t.seam.iT τ) := by
      have h1 := hn τ
      simp only [he] at h1
      exact_mod_cast h1
    have hka : Formalism.L2.Col.Fields.embC t.X t.seam.σ₀ τ (k' : t.X.E) = TaylorLogMetric.embT D (t.seam.iT τ) (k : D.host.E) := by
      rw [← hik]; exact t.seam_ok.1 τ _
    have h1 := congrArg (TaylorLogMetric.embT D (t.seam.iT τ)) hk
    rw [map_mul] at h1
    rw [GlobalTheory.Mem.Chr.DetGroupModel.emb_conj] at h1
    rw [hka]
    have h0 : TaylorLogMetric.embT D (t.seam.iT τ) (k : D.host.E) ≠ 0 := by simp
    generalize TaylorLogMetric.embT D (t.seam.iT τ) (k : D.host.E) = a at *
    generalize TaylorLogMetric.embT D (t.seam.iT τ) (z : D.host.E) = b at *
    have hn' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0
    have h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = b := by
      rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn'), ← h2]
      linear_combination (-a) * h1
    rw [hme, zpow_mul, h3, zpow_neg, inv_inv]
  have htw : (t.O u μ).mt (i + 1) (A.q (ratId t.X.F t.X.E k')) = D.muTil (i + 1) (A.q (ratId t.X.F t.X.E k')) := by
    by_cases h0 : μ = D.what₂.mu0
    · rw [(hP.ref h0).2]
    · obtain ⟨ξ, hξ, hmt⟩ := hP.tw μ h0 rfl
      rw [hmt u, twMt, if_pos ⟨by omega, by omega⟩, MonoidHom.mul_apply, hξ]
      have h1 : ((t.tup μ : Chr t.X.F t.X.E t.X.K)) (ratId t.X.F t.X.E k') = 1 := by
        have hm := (t.tup μ).2
        exact hm.1.1.1.1.1 ⟨k', rfl⟩
      rw [h1, map_one, mul_one]
  rw [← hq, htw, hmu]

end GlobalTheory.TwV

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.L2.Forms

noncomputable section

namespace GlobalTheory.TieFinOrd



theorem mt_finite_order : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m, ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E → ∃ n : ℕ, 0 < n ∧ (t.O u μ).mt (i + 1) (dtU y) ^ n = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H T i hi y hint
  classical
  letI := D.host.cmStar
  have hzU : Matrix.GeneralLinearGroup.det y.1 ∈ U1 (sigD D) := det_in_unitary_one D.host.F D.host.E (sigD D) 1 1 (by simp) y.1 y.2
  set z := Matrix.GeneralLinearGroup.det y.1 with hz
  have hconj : conjId (sigD D) z = z⁻¹ := by
    have h1 : z * conjId (sigD D) z = 1 := hzU
    exact eq_inv_of_mul_eq_one_right h1
  have hh90 : h90 (sigD D) z = Matrix.GeneralLinearGroup.det (y * y).1 := by
    show z / conjId (sigD D) z = _
    rw [hconj, div_inv_eq_mul]
    show _ = Matrix.GeneralLinearGroup.det (y.1 * y.1)
    rw [map_mul]
  set x : (AfE t.X.F t.X.E)ˣ := Units.map A.iA.symm.toRingHom.toMonoidHom z with hxdef
  have hxx : Units.map A.iA.toRingHom.toMonoidHom x = z := by
    ext
    simp [x]
  have hq : A.q x = dtU (y * y) := H.q_dt x (y * y) (by rw [hxx, hh90])
  have hcoe : ∀ w : AfE t.X.F t.X.E, A.iA w ∈ RInt D.host.F D.host.E ↔ w ∈ RInt t.X.F t.X.E := H.iA_int
  have hxint : x ∈ intU t.X.F t.X.E := by
    refine ⟨(hcoe _).1 ?_, (hcoe _).1 ?_⟩
    · simpa [x] using hint.1
    · simpa [x] using hint.2
  have hiso : IsAdIso (GlobalTheory.Mem.Col2.afIso t.X.F t.X.E) :=
    ⟨GlobalTheory.Mem.Col2.afIso_tmul_one _ _, GlobalTheory.Mem.Col2.mem_rInt_iff _ _⟩
  have hmu : ∃ n : ℕ, 0 < n ∧ D.muTil (i + 1) (A.q x) ^ n = 1 := by
    rw [H.muTil _ hiso ⟨i, hi⟩ (GlobalTheory.Mem.ReadEx.toIdl t.X.F t.X.E x) x (fun w => rfl) (GlobalTheory.Mem.ReadEx.toIdl_snd x).symm]
    exact GlobalTheory.HeckeFin.finite_order _ _ _ (fun w => rfl) ((GlobalTheory.Mem.ReadEx.mem_intU_iff x).1 hxint)
  obtain ⟨n, hn, hmun⟩ := hmu
  have hsq : (t.O u μ).mt (i + 1) (dtU y) ^ 2 = (t.O u μ).mt (i + 1) (A.q x) := by
    rw [hq, map_mul, map_mul, sq]
  by_cases hμ : μ = D.what₂.mu0
  · refine ⟨2 * n, by omega, ?_⟩
    rw [pow_mul, hsq, (H.ref hμ).2]
    exact hmun
  · obtain ⟨ξ, hξ, hmt⟩ := H.tw μ hμ rfl
    have htor := (t.tup μ).2
    simp only [tupGrp, finChar, Subgroup.mem_inf] at htor
    obtain ⟨k, hk, hkk⟩ := (isOfFinOrder_iff_pow_eq_one).1 htor.1.1.1.2
    refine ⟨2 * (n * k), by positivity, ?_⟩
    rw [pow_mul, hsq, hmt u, twMt, if_pos ⟨by omega, by omega⟩, MonoidHom.mul_apply, mul_pow, pow_mul, hmun, one_pow, one_mul,
      hξ x, ← map_pow, mul_comm, pow_mul]
    have : ((t.tup μ : Chr t.X.F t.X.E t.X.K) x) ^ k = 1 := by
      rw [← MonoidHom.pow_apply, hkk, MonoidHom.one_apply]
    rw [this, one_pow, map_one]

end GlobalTheory.TieFinOrd
end
end

section

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.adelicMatrixCongruentOneAtPrime_mul_of_both : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Q : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (k k' : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))), GlobalTheory.TwU.CongAt Q n k → GlobalTheory.TwU.CongAt Q n k' → GlobalTheory.TwU.CongAt Q n (k * k') := by
  first | exact @GlobalTheory.CongProd.congAt_mul_prod | exact GlobalTheory.CongProd.congAt_mul_prod | (intros; apply GlobalTheory.CongProd.congAt_mul_prod <;> assumption)
end

section

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.residueCard_columnFieldPrimeToHostPrime_eq : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.Col.Fields) (s : Formalism.L2.Ker.Seam D X) (P : HeightOneSpectrum (𝓞 X.E)), Formalism.L2.Col.qOf (GlobalTheory.TwU.seamP s P) = Formalism.L2.Col.qOf P := by
  first | exact @GlobalTheory.qOf_seamP | exact GlobalTheory.qOf_seamP | (intros; apply GlobalTheory.qOf_seamP <;> assumption)
end
