module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle814
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle572
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle721
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle440
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle815
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle640
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle803
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle783
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusPotentialCocycleClass
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle630
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle813
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletionFiltrationIffDeRhamFiltration
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle816
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
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ExtClass

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
  {T Tp U : LocLat (Gl l) ℚ_[l] K O} {f : LatHom T.L Tp.L} {g : LatHom Tp.L U.L}


omit [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in
theorem map_injective (hfg : IsSESLat (Qp := ℚ_[l]) f g) (B : Type) [AddCommGroup B] [Module O B] :
    Function.Injective (TensorProduct.map (LinearMap.id : B →ₗ[O] B) ((f.f.restrictScalars O).restrict f.T_le)) := by
  obtain ⟨h1, -, h3, h4, h5⟩ := hfg
  have := U.L.free
  refine LinearMap.lTensor_injective_of_exact_of_flat ((g.f.restrictScalars O).restrict g.T_le) (fun z => ?_)
    ((f.f.restrictScalars O).restrict f.T_le) (fun x y h => Subtype.ext (h1 (congrArg Subtype.val h)))
    (fun z => ⟨fun h => ?_, ?_⟩) B
  · obtain ⟨x, hx, h⟩ := h3 z.1 z.2
    exact ⟨⟨x, hx⟩, Subtype.ext h⟩
  · obtain ⟨y, hy⟩ := (h4 z.1).1 (congrArg Subtype.val h)
    exact ⟨⟨y, h5 y (hy ▸ z.2)⟩, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩
    exact Subtype.ext ((h4 _).2 ⟨y.1, rfl⟩)

theorem exists_solution {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {R : PhiMod O K l e a μ}
    {I : Ident t ϖ P T} {Ip : Ident t ϖ Q Tp} {Iu : Ident t ϖ R U} {F : GlobalTheory.BK.Hom P Q} {G : GlobalTheory.BK.Hom Q R}
    (hfg : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I Ip f F) (hG : IsMapOf Ip Iu g G) (u : ME R) (x : ↥U.L.T)
    (hux : toW t ϖ R u = Iu.ofT x) (k : ℕ) {x₂ : Vec K a κ} (hx₂ : x₂ ∈ Q.M) (hGx : G.app x₂ = k • u.1)
    (v : ↥Tp.L.T) (hv : g.f v = x.1) {y : Vec K a ι} (hy : y ∈ ME P) (hFy : F.app y = Q.phi x₂ - x₂) :
    ∃ m₀, phiW t ϖ P m₀ - m₀ = toW t ϖ P ⟨y, hy⟩ ∧
      homW t ϖ F m₀ = toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩ - k • Ip.ofT v := by
  obtain ⟨m₁, hm₁⟩ := I.exists_phiW_sub (toW t ϖ P ⟨y, hy⟩)
  have hfixp : ∀ z, phiW t ϖ Q (Ip.ofT z) = Ip.ofT z := fun z =>
    mem_Treal.1 (by rw [← Ip.range_ofT]; exact ⟨z, rfl⟩)
  have hfix : ∀ z, phiW t ϖ P (I.ofT z) = I.ofT z := fun z =>
    mem_Treal.1 (by rw [← I.range_ofT]; exact ⟨z, rfl⟩)
  have h1 : phiW t ϖ Q (homW t ϖ F m₁) - homW t ϖ F m₁ =
      phiW t ϖ Q (toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩) - toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩ := by
    rw [← homW_phiW, ← map_sub, hm₁, homW_toW, ← toW_phi t ϖ Q hx₂, ← map_sub]
    exact congrArg _ (Subtype.ext hFy)
  have h2 : homW t ϖ F m₁ - (toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩ - k • Ip.ofT v) ∈ LinearMap.range Ip.ofT := by
    rw [Ip.range_ofT, mem_Treal, map_sub, map_sub, map_nsmul, hfixp, sub_eq_iff_eq_add.1 h1]
    abel
  obtain ⟨z, hz⟩ := h2
  have h3 : homW t ϖ G (homW t ϖ F m₁) = 0 := by
    apply Iu.j.injective
    rw [hG, hF, map_zero]
    induction I.j m₁ using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul w s =>
      have h0 : ((g.f.restrictScalars O).restrict g.T_le) (((f.f.restrictScalars O).restrict f.T_le) s) = 0 :=
        Subtype.ext ((hfg.2.2.2.1 _).2 ⟨s.1, rfl⟩)
      simp only [latW, TensorProduct.map_tmul, h0, TensorProduct.tmul_zero]
    | add p q hp hq => simp only [map_add (f := _), hp, hq, add_zero]
  have h4 : homW t ϖ G (toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩) = k • Iu.ofT x := by
    rw [homW_toW, ← hux, ← map_nsmul]
    exact congrArg _ (Subtype.ext hGx)
  have h5 : homW t ϖ G (Ip.ofT v) = Iu.ofT x := by
    rw [hG.homW_ofT]
    exact congrArg _ (Subtype.ext hv)
  have h6 := congrArg (homW t ϖ G) hz
  rw [map_sub, map_sub, map_nsmul, h3, h4, h5, sub_self, sub_self, hG.homW_ofT, ← map_zero Iu.ofT] at h6
  obtain ⟨s, hs⟩ := (hfg.2.2.2.1 z.1).1 (congrArg Subtype.val (Iu.ofT_injective h6))
  have hsT : s ∈ T.L.T := hfg.2.2.2.2 s (hs ▸ z.2)
  refine ⟨m₁ - I.ofT ⟨s, hsT⟩, ?_, ?_⟩
  · rw [map_sub, hfix, ← hm₁]
    abel
  · rw [map_sub, hF.homW_ofT, show (⟨f.f (⟨s, hsT⟩ : ↥T.L.T), f.T_le _ hsT⟩ : ↥Tp.L.T) = z from Subtype.ext hs, hz]
    abel

theorem isCrisVal_toW {P : PhiMod O K l e a ι} (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) {w : Vec K a ι}
    (hL : w ∈ P.L) (hS : w ∈ P.MMl) :
    IsCrisVal t ϖ P jB (toW t ϖ P ⟨w, mem_ME_of_mem_L hL⟩) (jB (toBcris t ϖ P ⟨w, hS⟩)) := by
  refine ⟨1, fun i => ϖ.iTot t K (coordL P (A O K) ⟨_, hL⟩ i), by rw [map_one]; exact isUnit_one, ?_, ?_⟩
  · rw [map_one, one_smul]
    exact (toW_toCris_of_mem_L t ϖ P hL (P.ext_mono (A_le_S l e) hL)).1
  · rw [map_one, one_smul]
    refine congrArg _ (funext fun i => ?_)
    rw [toBcris_apply, toB, AlgHom.comp_apply, ← ϖ.iC_of_mem t K, ← ϖ.iB_of_mem t K]
    rfl

variable [TameDescentExponentData K l e a] {η H : ℕ}



theorem classOf {D : BKDat O K l e a ι η H} {Dp : BKDat O K l e a κ η H} {Du : BKDat O K l e a μ η H}
    (R : GalDat t ϖ (sQ l) D T) (Rp : GalDat t ϖ (sQ l) Dp Tp) (Ru : GalDat t ϖ (sQ l) Du U)
    (F : BKHom D Dp) (G : BKHom Dp Du) (hfg : IsSESLat (Qp := ℚ_[l]) f g)
    (hF : IsMapOf R.I Rp.I f F.toHom) (hG : IsMapOf Rp.I Ru.I g G.toHom) (hinj : Function.Injective F.app)
    (u : ME Du.toPhiMod) (x : ↥U.L.T) (hux : toW t ϖ Du.toPhiMod u = Ru.I.ofT x) (n : ℕ) {x₂ : Vec K a κ}
    (hx₂ : x₂ ∈ Dp.Minv) (hGx : G.app x₂ = (l ^ n) • u.1) {v : Tp.V} {c : Gl l → T.V} (hv : v ∈ Tp.L.T)
    (hgv : g.f v = x.1) (hc : ∀ h, Tp.ρ h v - v = f.f (c h)) {σ : Vec K a ι} (hσ : σ ∈ D.MMl)
    (hσi : σ ∈ D.desc.inv) (hFσ : F.app σ = Dp.phi x₂ - Dp.xi (red (Dp.phi x₂))) {y : Vec K a ι} (hy : y ∈ D.Y)
    (hFy : F.app y = Dp.phi x₂ - x₂) : R.ClassOf y ((l : K) ^ n • c) := by
  have hyE : y ∈ ME D.toPhiMod := BKDat.mem_invE_of_mem_Y hy
  obtain ⟨m₀, hm₀, hFm₀⟩ := exists_solution hfg hF hG u x hux (l ^ n) hx₂.1 hGx ⟨v, hv⟩ hgv hyE hFy
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.GalPot.exists_isCrisVal R hy hyE m₀ hm₀
  have hz : D.conn σ = D.zeta y := by
    apply hinj
    rw [F.toHom.app_conn, F.toHom.app_zeta, hFσ, hFy, PhiMod.zeta_phi_sub, map_sub, PhiMod.conn_xi, sub_zero]
  refine ⟨_, ⟨hyE, m₀, ⟨σ, hσ⟩, b₀, hm₀, hσi, hz, hb₀, rfl⟩, ?_⟩
  have hAS : A O K ≤ invL l (S O K e) := (A_le_S l e).trans (le_away _ _)
  have hL := Dp.phi_mem_L hx₂.1
  have hS : Dp.phi x₂ ∈ Dp.MMl := Dp.ext_mono hAS hL
  have hFS : F.app σ ∈ Dp.MMl := F.toHom.app_mem_ext hAS hσ
  have hξ : Dp.xi (red (Dp.phi x₂)) ∈ Dp.MMl := by
    have := sub_mem hS hFS
    rwa [hFσ, sub_sub_cancel] at this
  have hfixξ := GlobalTheory.GalPot.fix_of_horiz Rp ⟨_, hξ⟩ (fun γ => by
    change Dp.desc.act γ (Dp.xi _) = Dp.xi _
    rw [Descent.act_xi, ← Descent.red_act, Dp.desc.act_phi, hx₂.2 γ]) (Dp.conn_xi _)
  have N := GlobalTheory.T.bcrisTensorIdentification_natural l a e O K t ϖ ι D.toPhiMod T R.I R.jB R.cmp κ Dp.toPhiMod Tp Rp.I Rp.jB f
    F.toHom Rp.cmp hF
  have C := (GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ κ Dp.toPhiMod Tp Rp.I).2 Rp.jB Rp.cmp
  set Φ := TensorProduct.map (R := O) (LinearMap.id (R := O) (M := OB l O))
    ((f.f.restrictScalars O).restrict f.T_le) with hΦ
  have hfix : phiW t ϖ Dp.toPhiMod (Rp.I.ofT ⟨v, hv⟩) = Rp.I.ofT ⟨v, hv⟩ :=
    mem_Treal.1 (by rw [← Rp.I.range_ofT]; exact ⟨_, rfl⟩)
  have h1 := N.2 _ _ hb₀
  rw [homW_phiW, hFm₀, map_sub, map_nsmul, hfix, ← toW_phi t ϖ Dp.toPhiMod hx₂.1] at h1
  have h2 := C.2.1 _ _ _ h1 (IsCrisVal.sub t ϖ (isCrisVal_toW Rp.jB hL hS)
    (GlobalTheory.GalPot.isCrisVal_nsmul (C.2.2.2.1 ⟨v, hv⟩) (l ^ n)))
  have h3 : Φ (R.jB (toBcris t ϖ D.toPhiMod ⟨σ, hσ⟩) - b₀) =
      (l ^ n) • ((1 : OB l O) ⊗ₜ[O] (⟨v, hv⟩ : ↥Tp.L.T)) - Rp.jB (toBcris t ϖ Dp.toPhiMod ⟨_, hξ⟩) := by
    rw [map_sub, h2, ← N.1 ⟨σ, hσ⟩ ⟨_, hFS⟩ rfl,
      show (⟨F.app σ, hFS⟩ : Dp.MMl) = ⟨_, hS⟩ - ⟨_, hξ⟩ from Subtype.ext hFσ, map_sub, map_sub]
    abel
  intro γ k s hs
  apply map_injective hfg (OB l O)
  have hact : actB (sQ l) Tp γ ((1 : OB l O) ⊗ₜ[O] (⟨v, hv⟩ : ↥Tp.L.T)) =
      (1 : OB l O) ⊗ₜ[O] (Tp.actT γ ⟨v, hv⟩) := by
    rw [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]
  have hs' : (f.f.restrictScalars O).restrict f.T_le s = (l : O) ^ k • (l : O) ^ n • (Tp.actT γ ⟨v, hv⟩ - ⟨v, hv⟩) := by
    have hsm : ∀ (j : ℕ) (w : Tp.V), ((l : O) ^ j) • w = (l : K) ^ j • w := fun j w => by
      rw [← algebraMap_smul K ((l : O) ^ j) w, map_pow, map_natCast]
    apply Subtype.ext
    change f.f (s : T.V) = (l : O) ^ k • (l : O) ^ n • (Tp.ρ γ v - v)
    rw [hs, hsm, hsm, hc, Pi.smul_apply, map_smul, map_smul]
  rw [map_smul, map_sub, GlobalTheory.CocycleNat.actB_map, ← hΦ, h3, map_sub, map_nsmul, hfixξ, hact, hΦ,
    TensorProduct.map_tmul, LinearMap.id_apply, hs', TensorProduct.tmul_smul, TensorProduct.tmul_smul,
    TensorProduct.tmul_sub, smul_sub, ← Nat.cast_smul_eq_nsmul O, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
  congr 1
  abel



theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (T Tp : QLat LL) (f : LatHom T.L Tp.L) (g : LatHom Tp.L (unitLat (Gl l) : QLat LL).L), IsSESLat (Qp := ℚ_[l]) f g → ∀ (Pk : Pack a ϖ η H T) (Pp : Pack a ϖ η H Tp) (Pu : Pack a ϖ η H (unitLat (Gl l) : QLat LL)) (F : BKHom Pk.D Pp.D) (G : BKHom Pp.D Pu.D), IsMapOf Pk.R.I Pp.R.I f F.toHom → IsMapOf Pp.R.I Pu.R.I g G.toHom → IsExactTriple F.toHom G.toHom → Function.Injective F.app → ∀ (u : ME Pu.D.toPhiMod) (x : ↥(unitLat (Gl l) : QLat LL).L.T), x.1 = (1 : ↥LL.1) → u.1 ∈ Pu.D.Minv → Pu.D.phi u.1 = u.1 → toW (thetaW a LL) ϖ Pu.D.toPhiMod u = Pu.R.I.ofT x → ∀ (n : ℕ) (x₂ : Vec ↥LL.1 a (Fin Pp.n)), x₂ ∈ Pp.D.Minv → G.app x₂ = (l ^ n) • u.1 → ∀ (v : Tp.V) (c : Gl l → T.V), v ∈ Tp.L.T → g.f v = (1 : ↥LL.1) → (∀ h, Tp.ρ h v - v = f.f (c h)) → ∀ σ ∈ Pk.D.MMl, σ ∈ Pk.D.desc.inv → F.app σ = Pp.D.phi x₂ - Pp.D.xi (red (Pp.D.phi x₂)) → ∀ y ∈ Pk.D.Y, F.app y = Pp.D.phi x₂ - x₂ → Pk.R.ClassOf y ((l : ↥LL.1) ^ n • c) := by
  intro l _ a e _ _ ϖ LL _ _ η H T Tp f g hfg Pk Pp Pu F G hF hG _ hinj u x hx1 _ _ hux n x₂ hx₂ hGx₂ v c hv hgv hc σ hσ hσi hFσ y hy hFy
  exact classOf Pk.R Pp.R Pu.R F G hfg hF hG hinj u x hux n hx₂ hGx₂ hv (hgv.trans hx1.symm) hc hσ hσi hFσ hy hFy

end GlobalTheory.ExtClass
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem strat_defect_map {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d d' : ℕ} (S : Strat bk d)
    (S' : Strat bk d') (Y : Matrix (Fin d') (Fin d) bk.S) {B C : Obj l ↥(OL K)} (σ : Hom B C)
    (f g : Hom bk.prism B) :
    (S'.ε f g * Y.map (BK.hf g) - Y.map (BK.hf f) * S.ε f g).map σ.f =
      S'.ε (σ.comp f) (σ.comp g) * Y.map (BK.hf (σ.comp g)) -
        Y.map (BK.hf (σ.comp f)) * S.ε (σ.comp f) (σ.comp g) := by
  have e1 : (Y.map (BK.hf g)).map σ.f = Y.map (BK.hf (σ.comp g)) := rfl
  have e2 : (Y.map (BK.hf f)).map σ.f = Y.map (BK.hf (σ.comp f)) := rfl
  have m1 := Matrix.map_mul (L := S'.ε f g) (M := Y.map (BK.hf g)) (f := σ.f)
  have m2 := Matrix.map_mul (L := Y.map (BK.hf f)) (M := S.ε f g) (f := σ.f)
  rw [Matrix.map_sub _ (map_sub σ.f), m1, m2, S'.ε_nat, S.ε_nat, e1, e2]

theorem matrix_phi_eq_family_self (C : Type) [CommRing C] (φ : C → C) (e e' : C) (he : Associated e e')
    (d d' a a' b : ℕ) (P : Matrix (Fin d') (Fin d') C) (Q Q' : Matrix (Fin d) (Fin d) C)
    (hQ : Q * Q' = e' ^ b • (1 : Matrix (Fin d) (Fin d) C)) (Δ : Matrix (Fin d') (Fin d) C)
    (h : e' ^ a • (P * Δ.map φ) = e ^ a' • (Δ * Q)) :
    ∃ (h : ℕ) (c : Fin d' × Fin d → Fin d' × Fin d → C), ∀ j : Fin d' × Fin d,
      e ^ h * Δ j.1 j.2 = ∑ k : Fin d' × Fin d, φ (Δ k.1 k.2) * c k j :=
  GlobalTheory.T.matrix_phi_equation_to_family_equation C C (RingHom.id C) φ e e' he d d' a a' b P Q Q' hQ Δ h

theorem obj_eq_zero_of_pow_dvd {l : ℕ} [Fact l.Prime] {K : FinExt l} (B : Obj l ↥(OL K)) (x : B.A)
    (hk : ∀ k : ℕ, ((l : ℕ) : B.A) ^ k ∣ x) : x = 0 := by
  refine B.complete.toIsHausdorff.haus _ fun n => ?_
  obtain ⟨y, hy⟩ := hk n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hy]
  exact Ideal.mul_mem_right _ _
    (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) n)

theorem strat_map_A_mul {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d)
    {B : Obj l ↥(OL K)} (g : Hom bk.prism B) :
    S.A.map (BK.hf g) * S.A'.map (BK.hf g) = BK.hf g bk.E ^ S.b • (1 : Matrix (Fin d) (Fin d) B.A) := by
  rw [← Matrix.map_mul, S.A_mul]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem env_matrix_eq_zero {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K}
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) {d d' : ℕ} (S : Strat bk d) (S' : Strat bk d')
    (Δ : Matrix (Fin d') (Fin d) En.Q.A)
    (h1 : BK.hf En.inr bk.E ^ S.a • (S'.A.map (BK.hf En.inl) * Δ.map En.Q.D.φ) =
      BK.hf En.inl bk.E ^ S'.a • (Δ * S.A.map (BK.hf En.inr)))
    (hσ : ∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι →
      σ.comp En.inr = (ainfHom K g).comp bk.ι → Δ.map σ.f = 0) : Δ = 0 := by
  have hass := (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk En.Q En.inl En.inr).2.1
  obtain ⟨h, c, hc⟩ := matrix_phi_eq_family_self En.Q.A En.Q.D.φ _ _ hass d d' S.a S'.a S.b
    (S'.A.map (BK.hf En.inl)) _ _ (strat_map_A_mul S En.inr) Δ h1
  refine Matrix.ext fun i j => obj_eq_zero_of_pow_dvd En.Q (Δ i j) fun k => ?_
  refine GlobalTheory.T.breuilKisin_envelope_frobenius_solutions_pow_dvd l K bk En (Fin d' × Fin d) c h k (fun p => Δ p.1 p.2) hc ?_ (i, j)
  intro g σ ha hb p
  have h0 : σ.f (Δ p.1 p.2) = 0 := congrFun (congrFun (hσ g σ ha hb) p.1) p.2
  exact ⟨0, h0.trans (mul_zero _).symm⟩

theorem strat_eps_compat_env (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d')
    (Y : Matrix (Fin d') (Fin d) bk.S)
    (hφ : bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A))
    (hg : ∀ g : ↥(GK K), S'.ε bk.ι ((ainfHom K g).comp bk.ι) * Y.map (BK.hf ((ainfHom K g).comp bk.ι)) =
      Y.map (BK.hf bk.ι) * S.ε bk.ι ((ainfHom K g).comp bk.ι)) :
    S'.ε En.inl En.inr * Y.map (BK.hf En.inr) = Y.map (BK.hf En.inl) * S.ε En.inl En.inr := by
  have h1 := GlobalTheory.T.stratifiedHom_defect_frobenius_equation l K bk d d' S S' Y hφ En.Q En.inl En.inr
  have hσ : ∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι →
      σ.comp En.inr = (ainfHom K g).comp bk.ι →
      (S'.ε En.inl En.inr * Y.map (BK.hf En.inr) - Y.map (BK.hf En.inl) * S.ε En.inl En.inr).map σ.f = 0 := by
    intro g σ ha hb
    rw [strat_defect_map, ha, hb, hg g, sub_self]
  exact sub_eq_zero.1 (env_matrix_eq_zero En S S' _ h1 hσ)

end GlobalTheory.BSP
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FieldTransport

section General
variable {G H : Type} [Group G] [Group H]

def compEquiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ H V} {τ : Representation ℂ H W} (φ : ρ.Equiv τ) (f : G →* H) :
    Representation.Equiv (ρ.comp f : Representation ℂ G V) (τ.comp f : Representation ℂ G W) :=
  .mk φ.toLinearEquiv fun g => LinearMap.ext fun v => by
    have := congrArg (fun L => L v) (φ.toIntertwiningMap.isIntertwining' (f g))
    simpa using this

def compCompEquiv {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (f : H →* G)
    (g : G →* H) (h : ∀ x, f (g x) = x) : Representation.Equiv ((ρ.comp f).comp g : Representation ℂ G V) ρ :=
  .mk (LinearEquiv.refl ℂ V) fun x => LinearMap.ext fun v => by simp [h]

variable [TopologicalSpace G] [TopologicalSpace H]

def pullRep (f : G →* H) (hf : Continuous f) (hs : Function.Surjective f) (σ : IrrRep H) : IrrRep G :=
  ⟨σ.V, σ.ρ.comp f, fun v => (σ.smooth v).preimage hf,
    GlobalTheory.JacFactor.isIrreducible_comp_surj σ.ρ f hs σ.irr⟩

end General

section GLmap
variable {R S : Type} [CommRing R] [CommRing S]

abbrev mapGL (e : R ≃+* S) (n : ℕ) : GL (Fin n) R →* GL (Fin n) S := GeneralLinearGroup.map e.toRingHom

theorem mapGL_symm_mapGL (e : R ≃+* S) (n : ℕ) (g : GL (Fin n) R) : mapGL e.symm n (mapGL e n g) = g := by
  ext a b; simp [mapGL]

theorem mapGL_mapGL_symm (e : R ≃+* S) (n : ℕ) (g : GL (Fin n) S) : mapGL e n (mapGL e.symm n g) = g := by
  ext a b; simp [mapGL]

theorem mapGL_surjective (e : R ≃+* S) (n : ℕ) : Function.Surjective (mapGL e n) :=
  fun g => ⟨_, mapGL_mapGL_symm e n g⟩

theorem continuous_mapGL [TopologicalSpace R] [TopologicalSpace S] (e : R ≃+* S) (he : Continuous e) (n : ℕ) :
    Continuous (mapGL e n) :=
  Units.continuous_map (continuous_id.matrix_map he)

end GLmap
end GlobalTheory.FieldTransport

namespace GlobalTheory.FieldTransport

section Fields
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

def transportFun (i : k ≃+* k') (hi' : Continuous i.symm) (x : IrrGL (k := k)) : IrrGL (k := k') :=
  ⟨x.1, (pullRep (mapGL i.symm x.1) (continuous_mapGL i.symm hi' x.1) (mapGL_surjective i.symm x.1) x.2.rep).cl⟩

theorem transportFun_left (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm) (x : IrrGL (k := k)) :
    transportFun i.symm (by simpa using hi) (transportFun i hi' x) = x := by
  refine congrArg (Sigma.mk x.1) ((IrrRep.cl_eq_iff.2 ?_).trans x.2.cl_rep)
  obtain ⟨ψ⟩ := IrrRep.nonempty_equiv_rep
    (pullRep (mapGL i.symm x.1) (continuous_mapGL i.symm hi' x.1) (mapGL_surjective i.symm x.1) x.2.rep)
  exact ⟨(compEquiv ψ (mapGL i.symm.symm x.1)).trans
    (compCompEquiv x.2.rep.ρ (mapGL i.symm x.1) (mapGL i.symm.symm x.1) fun g => mapGL_symm_mapGL i x.1 g)⟩

theorem repRel_iff (i : k ≃+* k') (hi' : Continuous i.symm) (x : IrrGL (k := k)) (x' : IrrGL (k := k')) :
    RepRel i x x' ↔ transportFun i hi' x = x' := by
  constructor
  · rintro ⟨n, π, π', e, rfl, rfl, he⟩
    refine congrArg (Sigma.mk n) (IrrRep.cl_eq_iff.2 ?_)
    obtain ⟨ψ⟩ := IrrRep.nonempty_equiv_rep π
    refine ⟨(compEquiv ψ (mapGL i.symm n)).trans (.mk e fun g => LinearMap.ext fun v => ?_)⟩
    have := he (mapGL i.symm n g) v
    rw [show GeneralLinearGroup.map i.toRingHom (mapGL i.symm n g) = g from mapGL_mapGL_symm i n g] at this
    simpa using this
  · rintro rfl
    refine ⟨x.1, x.2.rep, pullRep (mapGL i.symm x.1) (continuous_mapGL i.symm hi' x.1)
      (mapGL_surjective i.symm x.1) x.2.rep, LinearEquiv.refl ℂ _,
      congrArg (Sigma.mk x.1) x.2.cl_rep.symm, rfl, fun g v => ?_⟩
    show x.2.rep.ρ g v = x.2.rep.ρ (mapGL i.symm x.1 (mapGL i x.1 g)) v
    rw [mapGL_symm_mapGL]

theorem exists_transport (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm) :
    ∃ T : IrrGL (k := k) ≃ IrrGL (k := k'), (∀ x x', RepRel i x x' ↔ T x = x') ∧ ∀ x, (T x).1 = x.1 := by
  have hi2 : Continuous i.symm.symm := by simpa using hi
  refine ⟨⟨transportFun i hi', transportFun i.symm hi2, fun x => transportFun_left i hi hi' x, fun y => ?_⟩,
    repRel_iff i hi', fun x => rfl⟩
  have := transportFun_left i.symm hi' hi2 y
  simpa using this

end Fields
end GlobalTheory.FieldTransport


open GlobalTheory.FieldTransport in
theorem GlobalTheory.transport_irrGL_bijective : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∃ T : IrrGL (k := k) ≃ IrrGL (k := k'), (∀ x x', RepRel i x x' ↔ T x = x') ∧ ∀ x, (T x).1 = x.1 := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi
  exact exists_transport i hi (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi).1
end
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.DivPtFourier

open scoped Classical

variable {D : D7} {S T : HSp D}

def divPts (Λ : AddSubgroup (WO S T)) (c : AE D) (N : ℕ) : AddSubgroup (WO S T) where
  carrier := {y | c • y = y ∧ N • y ∈ Λ}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [smul_add, hx1, hy1], by rw [nsmul_add]; exact Λ.add_mem hx2 hy2⟩
  zero_mem' := ⟨smul_zero _, by rw [nsmul_zero]; exact Λ.zero_mem⟩
  neg_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨by rw [smul_neg, hx1], by rw [smul_neg]; exact Λ.neg_mem hx2⟩

theorem mem_divPts {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} {y : WO S T} :
    y ∈ divPts Λ c N ↔ c • y = y ∧ N • y ∈ Λ := Iff.rfl

abbrev DQ (Λ : AddSubgroup (WO S T)) (c : AE D) (N : ℕ) :=
  ↥(divPts Λ c N) ⧸ (Λ ⊓ GlobalTheory.PlaceModel.half S T c).addSubgroupOf (divPts Λ c N)

noncomputable def rep {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} (q : DQ Λ c N) : ↥(divPts Λ c N) :=
  (QuotientAddGroup.mk_surjective q).choose

theorem mk_rep {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} (q : DQ Λ c N) :
    (QuotientAddGroup.mk (rep q) : DQ Λ c N) = q :=
  (QuotientAddGroup.mk_surjective q).choose_spec

theorem rep_injective {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} :
    Function.Injective fun q : DQ Λ c N => ((rep q : ↥(divPts Λ c N)) : WO S T) := by
  intro q₁ q₂ h
  rw [← mk_rep q₁, ← mk_rep q₂, Subtype.ext h]

variable (ψ : AddChar (AF D.host.F) ℂ)

end GlobalTheory.DivPtFourier

namespace GlobalTheory.DivPtFourier

open scoped Classical

variable {D : D7} {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ)

end GlobalTheory.DivPtFourier

namespace GlobalTheory.DivPtFourier

open scoped Classical

end GlobalTheory.DivPtFourier
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completionFiltration_iff_deRhamFiltration : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl) (j : ℤ), GlobalTheory.BKGal.JumpDR.InEhat ↥(OL LL) ↥LL.1 l e j (GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1)) ↔ ∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (s k)) (X (jB (toBcris (thetaW a LL) ϖ P (m k)))) ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) j := by
  first | exact @GlobalTheory.BKGal.JumpDR.inEhat_iff_filV | exact GlobalTheory.BKGal.JumpDR.inEhat_iff_filV | (intros; apply GlobalTheory.BKGal.JumpDR.inEhat_iff_filV <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem _root_.GlobalTheory.T.weightSection_eq_zero_of_vanishing_finite_extensions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : Rul Xo c), h ∈ sec Xo c a n → (∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (y : FrPt Xo c L), evR Xo c h y = 0) → h = 0 := by
  first | exact @GlobalTheory.Reg.sec_eq_zero_of_finite_values | exact GlobalTheory.Reg.sec_eq_zero_of_finite_values | (intros; apply GlobalTheory.Reg.sec_eq_zero_of_finite_values <;> assumption)
end
