module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ComapLam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle002
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004

@[expose] public section

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.resid_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G.frame O n), (∀ a : G.G₀, g.p₀ a = 1 → ∀ i, r.chib i a = 1) → ∃ r' : Resid G'.frame O n, Glob.Compat g r r' ∧ ((∀ w, r.Ip w = G.frame.Iu w) → ∀ w, r'.Ip w = G'.frame.Iu w) := by
  intro l _ L G G' g n O _ _ _ r hker
  let c : Fin n → G'.frame.G₀ →* (ResidueField O)ˣ := fun i =>
    g.p₀.liftOfSurjective g.p₀_surj ⟨r.chib i, fun a ha => by
      rw [MonoidHom.mem_ker] at ha ⊢
      exact hker a ha i⟩
  have hca : ∀ i a, c i (g.p₀ a) = r.chib i a := fun i a =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a
  have hc : ∀ i, (c i).comp g.p₀ = r.chib i := fun i => by
    ext a
    simp only [MonoidHom.comp_apply, hca]
  have hdiag : (diagRep c).comp g.p₀ = diagRep r.chib := by
    ext a
    simp only [MonoidHom.comp_apply, diagRep, MonoidHom.coe_mk, OneHom.coe_mk, hca]
  have hD : (GDet.ofRep (diagRep c)).comap g.p₀ = GDet.ofRep (diagRep r.chib) := by
    rw [(comap_lam n (ResidueField O) _ _ g.p₀ (GDet.ofRep (diagRep c))).2.2.2.2.1 (diagRep c), hdiag]
  have key : ∀ (B : Type) [CommRing B] [Algebra (ResidueField O) B] (z : MonoidAlgebra B G.frame.G₀),
      (GDet.ofRep (diagRep c)).D B (MonoidAlgebra.mapDomainRingHom B g.p₀ z) =
        (GDet.ofRep (diagRep r.chib)).D B z := by
    intro B _ _ z
    calc (GDet.ofRep (diagRep c)).D B (MonoidAlgebra.mapDomainRingHom B g.p₀ z)
        = ((GDet.ofRep (diagRep c)).comap g.p₀).D B z := rfl
      _ = (GDet.ofRep (diagRep r.chib)).D B z := by rw [hD]
  let r' : Resid G'.frame O n :=
    { chib := c
      chib_open := fun i => by
        rw [← g.p₀_quot.isOpen_preimage]
        have hset : (g.p₀ ⁻¹' ((c i).ker : Set G'.frame.G₀)) = ((r.chib i).ker : Set G.frame.G₀) := by
          ext a
          simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, hca]
        rw [hset]
        exact r.chib_open i
      chib_inj := fun i j hij => by
        apply r.chib_inj
        rw [← hc i, ← hc j, hij]
      polar := by
        intro B _ _ _ _ y
        obtain ⟨x0, hx0⟩ := Finsupp.mapDomain_surjective (M := B) g.p₀_surj y.coeff
        have hx' : MonoidAlgebra.mapDomainRingHom B g.p₀ (MonoidAlgebra.ofCoeff x0) = y := by
          rw [MonoidAlgebra.mapDomainRingHom_apply]
          show MonoidAlgebra.ofCoeff (Finsupp.mapDomain _ x0) = y
          rw [hx0]
        rw [← hx', ← (map_star l L G G' g n O B).1 (MonoidAlgebra.ofCoeff x0), key, key]
        exact r.polar B _
      psib := r.psib
      psib_open := r.psib_open
      th := r.th
      th_comm := r.th_comm }
  refine ⟨r', ⟨fun i => (hc i).symm, rfl, rfl⟩, ?_⟩
  intro hIp w
  have hle : ∀ i, G.frame.Iu w ≤ (r.chib i).ker := by
    intro i
    have h1 := hIp w
    unfold Resid.Ip at h1
    exact (inf_eq_left.mp h1).trans (iInf_le _ i)
  unfold Resid.Ip
  apply inf_eq_left.mpr
  rw [le_iInf_iff]
  intro i
  rintro _ ⟨x, hx, rfl⟩
  show c i ((G'.φu w) x) = 1
  rw [← g.p₀_φu w x, hca]
  exact hle i ⟨x, hx, rfl⟩
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.koszulThree_of_det :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (al : Fin T.q → Fin n → x.A), T.ProL → T.Eig x al → K3 Λ.h k := by
  intro l _ L G0 T Λ n x k al hP hE
  intro z hz
  have hρ : ∀ g, x.ρX x.A g = mat x.ρ g := by
    intro g
    ext i j
    simp [NP.ρX]
  have hzero : ∀ j, z (Λ.ta j) = 0 := by
    intro j
    have hc := Λ.comm j
    have h1 := hz.2.2.1 (Λ.ph j) (Λ.ta j)
    have h2 := hz.2.2.1 (Λ.ta j) (Λ.ph j)
    rw [hc] at h1
    simp only [hρ, map_inv, Λ.p_ta, Λ.p_ph, map_one, inv_one, one_mul, mul_one] at h1 h2
    rw [h2] at h1
    have h3 : z (Λ.ta j) = mat x.ρ (T.sg j) * z (Λ.ta j) * mat x.ρ (T.sg j)⁻¹ := by
      have := h1
      rw [add_comm (z (Λ.ta j))] at this
      exact add_left_cancel this
    have hPZ : mat x.ρ (T.sg j) * z (Λ.ta j) = z (Λ.ta j) * mat x.ρ (T.sg j) := by
      conv_rhs => rw [h3]
      rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    exact od_comm x.A n x.a (mat x.ρ (T.sg j)) (z (Λ.ta j)) (al j) (x.blk _) (hz.1 _)
      (hE j).1 (hE j).2 hPZ
  obtain ⟨y, hy⟩ := coc_ker l L Λ.G G0 Λ.h n x (Set.range Λ.ta) z
    (by rw [← Set.range_comp]; exact ker_oo l L G0 T Λ hP)
    (by
      rintro a ⟨j, rfl⟩
      exact ⟨Λ.p_ta j, hzero j⟩)
    hz
  have hzy : (fun g => y (Λ.h.p₀ g)) = z := funext hy
  have hy' : y ∈ SelZ G0.frame x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a) := by
    rw [← Glob.Hom.sel_iff Λ.h, hzy]
    exact hz
  obtain ⟨s, c, hsc⟩ := k.gen y hy'
  refine ⟨s, c, ?_⟩
  have hb := (Glob.Hom.bd_iff Λ.h (x.ρX x.A) (Od x.A x.A n x.a) _).mpr hsc
  show _ ∈ Bd Λ.G.frame (fun g => x.ρX x.A (Λ.h.p₀ g)) (Od x.A x.A n x.a)
  convert hb using 1
  funext g
  simp [hy]
end
