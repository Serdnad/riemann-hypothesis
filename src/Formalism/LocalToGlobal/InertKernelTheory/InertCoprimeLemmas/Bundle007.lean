module

public import Formalism.LocalToGlobal.InertKernelTheory.Bundle008
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AlgKleinPf
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepFrame
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle012
public import Formalism.LocalToGlobal.InertKernelTheory.SclY
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepFrob
public import Formalism.LocalToGlobal.InertKernelTheory.ProjRSurj
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle003
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.NumberTheory.LSeries.PrimesInAP
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.L2.KerInert

namespace AlgTP

open NumberField Formalism.BasicNotions Formalism.L2.Ker

theorem exists_inert_prime (d : ℕ) (hd : d.Prime) (hd4 : d % 4 = 3) (n : ℕ) :
    ∃ p, n < p ∧ p.Prime ∧ jacobiSym (-(d : ℤ)) p = -1 := by
  have : NeZero (4 * d) := ⟨by have := hd.pos; omega⟩
  have hu : IsUnit (-1 : ZMod (4 * d)) := isUnit_one.neg
  obtain ⟨p, hpn, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu n
  refine ⟨p, hpn, hp, ?_⟩
  have hmod : (p : ℤ) ≡ -1 [ZMOD ((4 * d : ℕ) : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact hpa
  have hm4 : (p : ℤ) ≡ -1 [ZMOD 4] := by
    have h : (p : ℤ) ≡ -1 [ZMOD 4 * (d : ℤ)] := by simpa using hmod
    exact Int.ModEq.of_mul_right _ h
  have hmd : (p : ℤ) ≡ -1 [ZMOD (d : ℤ)] := by
    have h : (p : ℤ) ≡ -1 [ZMOD 4 * (d : ℤ)] := by simpa using hmod
    exact Int.ModEq.of_mul_left _ h
  have hp4 : p % 4 = 3 := by
    unfold Int.ModEq at hm4
    omega
  have hodd : Odd p := Nat.odd_iff.2 (by omega)
  have hdodd : Odd d := Nat.odd_iff.2 (by omega)
  rw [jacobiSym.neg _ hodd, ZMod.χ₄_nat_three_mod_four hp4,
    jacobiSym.quadratic_reciprocity_three_mod_four hd4 hp4, jacobiSym.mod_left' hmd,
    jacobiSym.at_neg_one hdodd, ZMod.χ₄_nat_three_mod_four hd4]
  norm_num

theorem mem_one_iff {E : Type} [Field E] [NumberField E] (w : E) :
    w ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ w := by
  rw [Submodule.mem_one]
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).symm

theorem mem_range_iff {E : Type} [Field E] [NumberField E] (w : E) :
    w ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ w := by
  rw [RingHom.mem_range]
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).symm

theorem exists_den (D : D7) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) :
    ∃ s : ℕ, 0 < s ∧ (∀ x ∈ L, (s : D.host.E) • x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N) ∧
      ∀ x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N, (s : D.host.E) • x ∈ L := by
  let _ := D.host.cmStar
  classical
  obtain ⟨S, hS⟩ := hL.1
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (S.biUnion fun v => Finset.univ.image v)
  have hint : ∀ w ∈ S.biUnion (fun v => Finset.univ.image v), IsIntegral ℤ ((y.natAbs : D.host.E) * w) := by
    intro w hw
    have h := hy w hw
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq y with e | e
    · have : ((y.natAbs : ℤ) : D.host.E) = (y : D.host.E) := by rw [← e]
      rw [← this] at h
      simpa using h
    · have : ((y.natAbs : ℤ) : D.host.E) = -(y : D.host.E) := by
        rw [show ((y.natAbs : ℤ)) = -y by omega]; push_cast; ring
      have h' := h.neg
      rw [show -((y : D.host.E) * w) = ((y.natAbs : ℤ) : D.host.E) * w by rw [this]; ring] at h'
      simpa using h'
  have hfirst : ∀ x ∈ L, ((y.natAbs : ℕ) : D.host.E) • x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
    have hgen : ∀ v ∈ (S : Set (Fin N → D.host.E)), ((y.natAbs : ℕ) : D.host.E) • v ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
      intro v hv
      rw [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi]
      intro i _
      rw [mem_one_iff, Pi.smul_apply, smul_eq_mul]
      exact hint (v i) (Finset.mem_biUnion.2 ⟨v, hv, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
    intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem v hv => exact hgen v hv
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ r ha
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, hfirst, ?_⟩
  intro x hx
  refine (hL.2.2 _).2 ?_
  intro z hz
  have hz' := hfirst z hz
  rw [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi] at hx hz'
  have e : stdH D.host.E N z (((y.natAbs : ℕ) : D.host.E) • x) =
      stdH D.host.E N (((y.natAbs : ℕ) : D.host.E) • z) x := by
    unfold stdH
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_natCast]
    ring
  rw [e, mem_range_iff]
  unfold stdH
  refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ ?_
  · have h := (mem_one_iff _).1 (hz' i (Set.mem_univ i))
    have h2 := h.map (starRingEnd D.host.E).toIntAlgHom
    convert h2 using 1 <;> rfl
  · exact (mem_one_iff _).1 (hx i (Set.mem_univ i))

theorem algebraic_translates_all_data : AlgTAll := by
  intro D cc δ B χ hcc hδ hχ N N' L L' hA t ⟨a, ha, hat⟩ α
  obtain ⟨s, hs, hsL1, hsL2⟩ := exists_den D L hA.2.2.1
  obtain ⟨s', hs', hsL1', hsL2'⟩ := exists_den D L' hA.2.2.2
  have hd := D.host.hyp
  obtain ⟨p, hpn, hp, hJ⟩ :=
    exists_inert_prime D.host.d hd.2.1 (by have := hd.2.2.2.1; omega) (a * s * s' + 4)
  have : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < a * s * s' := by positivity
  have hcop : ∀ m : ℕ, m ∣ a * s * s' → Nat.Coprime m p := fun m hm =>
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
      absurd (Nat.le_of_dvd hpos (h.trans hm)) (by omega))
  have H := (AlgP.algebraic_fact_kernels D cc δ B hcc hδ χ hχ p (by omega) hJ N N').1 L L' hA
    ⟨s, hcop s (Dvd.intro_left _ rfl |>.mul_right _), hsL2, hsL1⟩
    ⟨s', hcop s' (Dvd.intro_left _ rfl), hsL2', hsL1'⟩ t
    ⟨a, ha, hcop a ((Dvd.intro _ rfl).mul_right _), hat⟩
  exact H.2 α

theorem algT_of {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) {χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ}
    (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : Formalism.MainNotions.TaylorLogMetric.IsChi D χ) : B.AlgT χ :=
  algebraic_translates_all_data D cc δ B χ hcc hδ hχ

end AlgTP

end Formalism.L2.KerInert
end
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.KG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F

theorem linSub_scl {σ R : Type} [Fintype σ] [CommRing R] (c : R) (A : σ → σ → R) (G : MvPowerSeries σ R) :
    Formalism.MainNotions.FormalGroupSystem.linSub (fun x y => c * A x y) G = Formalism.MainNotions.FormalGroupSystem.linSub A (Formalism.L2.KerInert.Rep.sclY c G) := by
  have ha : MvPowerSeries.HasSubst (fun k : σ =>
      (MvPowerSeries.C c * MvPowerSeries.X k : MvPowerSeries σ R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  have hb : MvPowerSeries.HasSubst (fun x : σ =>
      (∑ y, MvPowerSeries.C (A x y) * MvPowerSeries.X y : MvPowerSeries σ R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  unfold Formalism.MainNotions.FormalGroupSystem.linSub Formalism.L2.KerInert.Rep.sclY
  rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  congr 1
  funext k
  rw [← MvPowerSeries.coe_substAlgHom hb, map_mul, MvPowerSeries.coe_substAlgHom hb, MvPowerSeries.subst_C,
    MvPowerSeries.subst_X hb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← map_mul]

variable {p : ℕ} [Fact p.Prime]

theorem subBG_eq {X : Sys p} {D : D7} (E : CEmbC X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (fd : FData X D) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1))
    (x y : D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) :
    subBG E.toCEmb pos fd j La La' x y = Formalism.L2.KerInert.RepFrame.subGen X E pos fd.frM j La La' x y := by
  unfold subBG Formalism.L2.KerInert.RepFrame.subGen
  split_ifs <;> rfl

theorem ltC_eq (g : GL3Theta.G1 p) (hLT : LTIso g) :
    ltC g hLT = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹ := by
  unfold ltC Formalism.L2.KerInert.BeCob.eLT
  rw [mul_inv, Units.val_inv_eq_inv_val]

theorem twInt_all (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) : Formalism.L2.KerInert.RepFrame.TwInt X E := by
  intro v s w
  rw [Formalism.L2.KerInert.RepFrob.twE_eq, Formalism.L2.KerInert.RepFrob.twT_alg]
  exact Formalism.L2.G.Pend.norm_wToC_le p _


end Formalism.L2.KerInert.KG
end
end

section

noncomputable section

namespace Formalism.L2.KerInert.SecondKernelProjection

open Formalism.MainNotions.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Classical

section Sel

variable {K A B : Type} [Field K] [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

theorem secR_mem (R : Submodule K (A × B)) (a : R.map (LinearMap.fst K A B)) : ((a : A), secR R a) ∈ R := by
  have hs := Classical.choose_spec (LinearMap.exists_rightInverse_of_surjective (projR R)
    (LinearMap.range_eq_top.2 (projR_surj R)))
  set s := Classical.choose (LinearMap.exists_rightInverse_of_surjective (projR R)
    (LinearMap.range_eq_top.2 (projR_surj R))) with hsdef
  have h1 : projR R (s a) = a := LinearMap.congr_fun hs a
  have h2 : ((s a : R) : A × B).1 = (a : A) := congrArg Subtype.val h1
  have h3 : ((a : A), secR R a) = ((s a : R) : A × B) := Prod.ext h2.symm rfl
  rw [h3]
  exact (s a).2

theorem selOf_mem (R : Submodule K (A × B)) (a : A) (ha : a ∈ R.map (LinearMap.fst K A B)) : (a, selOf R a) ∈ R := by
  have hx := Classical.choose_spec (LinearMap.exists_extend (secR R))
  have h1 : selOf R a = secR R ⟨a, ha⟩ := LinearMap.congr_fun hx ⟨a, ha⟩
  rw [h1]
  exact secR_mem R ⟨a, ha⟩

end Sel

section Val

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {p : ℕ}
  {S : StepLevel F E σ J T f bad} {emb : Tau → E →+* ℂ} {G : GAtP p} {A : LocAt F E n G}
  {pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau}
  {V cls : Type} [AddCommGroup V] [Module ℂ V] {embV : V →ₗ[ℂ] (cls → Frames (gramC J emb) → ℂ)}
  {yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F)}

theorem isValV_uniq (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hi : EvInj emb G A pos (J := J))
    (hp : PtEx S G A yc) {x : V} {i : G.comp} {L : G.P.Tup} {Q Q' : XR G.P ℂ} (hL : G.P.IsLatTup L)
    (h : IsValV S emb G A pos embV yc x i L Q) (h' : IsValV S emb G A pos embV yc x i L Q') : Q = Q' := by
  choose g0 hg0 hLg using hL
  let g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v) := fun v => ((Matrix.isUnit_iff_isUnit_det _).2 (hg0 v)).unit
  have hg : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := hLg
  obtain ⟨c, γ, κ, hγ, hpt⟩ := hp i g
  have hz : evC G.P A.rk pos (gramC J emb) (crdB emb A.B) (Q - Q') = 0 := by
    funext z
    obtain ⟨z', hz'⟩ := frames_tr emb hc γ hγ z
    rw [map_sub, Pi.sub_apply, h g hg c γ hγ κ hpt z z' hz', h' g hg c γ hγ κ hpt z z' hz', sub_self]
    rfl
  exact sub_eq_zero.1 (hi _ hz)

theorem selOf_relV (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hi : EvInj emb G A pos (J := J))
    (hp : PtEx S G A yc) {x : V} {i : G.comp} {L : G.P.Tup} {Q : XR G.P ℂ} (hL : G.P.IsLatTup L)
    (h : IsValV S emb G A pos embV yc x i L Q) : selOf (relV S emb G A pos embV yc i L) x = Q :=
  isValV_uniq hc hi hp hL (selOf_mem (relV S emb G A pos embV yc i L) x (Submodule.mem_map.2 ⟨(x, Q), h, rfl⟩)) h

end Val

section Step

open Formalism.BasicNotions Formalism.MainNotions.G.CmpJ Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m}
  {G : GAtP p}

theorem embN_eq_nrmR (S : StepIn M i hi G) (β : S.Ch) (x : (M.lat i).V) : S.embN β x = nrmR S β (M.emb i x) := rfl

theorem rdS_cmpJ (S : StepIn M i hi G) {Kc : Type} [Field Kc] [iA : Algebra G.Kf Kc] (e : D.what₂.LL →+* G.Kf)
    (H : ∀ β, S.Core e β) (hS : BlockRationalityField) (ι : ℂ →+* Kc)
    (hι : ∀ r : D.what₂.LL, ι (D.what₂.embLL r) = algebraMap G.Kf Kc (e r)) (x : (M.lat i).V) (c' : G.comp) (L : G.P.Tup) :
    MvPolynomial.map (algebraMap G.Kf Kc) (S.cmpJ e x c' L) = rdS S ι c' L (M.emb i x) := by
  have hcmp : S.cmpJ e x c' L = cmpC (S.K (S.eC.symm c').1).lev (embT D) D.what₂.embLL (S.charts.gat (S.eC.symm c').1) e
      (S.loc (S.eC.symm c').1) S.pos (S.embN (S.eC.symm c').1) (S.K (S.eC.symm c').1).y x (S.eC.symm c').2 L := rfl
  rw [hcmp]
  by_cases hL : G.P.IsLatTup L
  · simp only [cmpC, rdS, hL, ↓reduceIte]
    have hH := (H (S.eC.symm c').1).toHyp hS
    have hv := valC_spec hH.ex x (S.eC.symm c').2 L hL
    have hV : IsValV (S.K (S.eC.symm c').1).lev (embT D) (S.charts.gat (S.eC.symm c').1) (S.loc (S.eC.symm c').1) S.pos
        (nrmR S (S.eC.symm c').1) (S.K (S.eC.symm c').1).y (M.emb i x) (S.eC.symm c').2 L
        (MvPolynomial.map D.what₂.embLL (valC (S.K (S.eC.symm c').1).lev (embT D) D.what₂.embLL (S.charts.gat (S.eC.symm c').1)
          (S.loc (S.eC.symm c').1) S.pos (S.embN (S.eC.symm c').1) (S.K (S.eC.symm c').1).y x (S.eC.symm c').2 L)) :=
      hv.2
    have hsel : selOf (relV (S.K (S.eC.symm c').1).lev (embT D) (S.charts.gat (S.eC.symm c').1) (S.loc (S.eC.symm c').1) S.pos
        (nrmR S (S.eC.symm c').1) (S.K (S.eC.symm c').1).y (S.eC.symm c').2 L) (M.emb i x) =
        MvPolynomial.map D.what₂.embLL (valC (S.K (S.eC.symm c').1).lev (embT D) D.what₂.embLL (S.charts.gat (S.eC.symm c').1)
          (S.loc (S.eC.symm c').1) S.pos (S.embN (S.eC.symm c').1) (S.K (S.eC.symm c').1).y x (S.eC.symm c').2 L) :=
      selOf_relV (embT_conj D) (evInj_pf (embT D) _ _ _) hH.ptEx hL hV
    rw [LinearMap.comp_apply]
    show _ = MvPolynomial.map ι (selOf (relV (S.K (S.eC.symm c').1).lev (embT D) (S.charts.gat (S.eC.symm c').1)
      (S.loc (S.eC.symm c').1) S.pos (nrmR S (S.eC.symm c').1) (S.K (S.eC.symm c').1).y (S.eC.symm c').2 L) (M.emb i x))
    have hcomp : (algebraMap G.Kf Kc).comp e = ι.comp D.what₂.embLL := RingHom.ext fun r => (hι r).symm
    rw [hsel, MvPolynomial.map_map, MvPolynomial.map_map, hcomp]
  · simp only [cmpC, rdS, hL, ↓reduceIte, map_zero, LinearMap.zero_apply]

end Step

section Cons

open Formalism.BasicNotions Formalism.MainNotions.G.CmpJ Formalism.L2.G

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

theorem trC_heq {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (hC : C = C') (i : ℕ) (φ : C'.cls i → C'.Y i → ℂ)
    (ψ : C.cls i → C.Y i → ℂ) (hφ : HEq φ ψ) : trC hC i φ = ψ := by
  subst hC
  exact eq_of_heq hφ

theorem rdJ_of_isValV (I : CmpJIn Tw u μ w h Lv) (hC : OnChain I) (H : CmpJHyp c I) (hS : BlockRationalityField) {Kc : Type} [Field Kc]
    (ι : ℂ →+* Kc) (j : ℕ) (hj : j + 1 ≤ D.R.m) (c' : Lv.comp (j + 1)) (L' : (Fl.Pj (j + 1)).Tup) (hL' : (Fl.Pj (j + 1)).IsLatTup L')
    (φ : (D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) (Q : XR (Fl.Pj (j + 1)) ℂ)
    (hQ : IsValV ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm c').1).lev (embT D)
      ((I.at' j hj).st.charts.gat ((I.at' j hj).st.eC.symm c').1) ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm c').1)
      (I.at' j hj).st.pos (nrmR (I.at' j hj).st ((I.at' j hj).st.eC.symm c').1)
      ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm c').1).y (trC (hC j hj) (j + 1) φ) ((I.at' j hj).st.eC.symm c').2 L' Q) :
    rdJ I hC ι j c' L' φ = MvPolynomial.map ι Q := by
  have hH := ((H.core j hj) ((I.at' j hj).st.eC.symm c').1).toHyp hS
  have hsel := selOf_relV (embT_conj D) (evInj_pf (embT D) _ _ _) hH.ptEx hL' hQ
  unfold rdJ
  rw [dite_eq_left hj]
  simp only [rdS, hL', ↓reduceIte]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  exact congrArg (MvPolynomial.map ι) hsel

end Cons

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances

theorem series_reading_entries : TieReadJ := by
  intro D L hT Gi Gl Kc0 Dx cX ex u μ w h _ Fl Lv Ch K I H hS Gt hCh hC std vp unif eO eO_spec dG dG_spec om Y ι hι j
    y c' L' _
  unfold rdJ
  by_cases hj : j + 1 ≤ D.R.m
  · rw [dite_eq_left hj]
    have h1 : (kerAtMu_any K H hS Gt Ch hCh).cmp (j + 1) y =
        (I.at' j hj).st.cmpJ (ex.cmp.embW u w h) ((I.at' j hj).eps.symm y) := kerAtMu_cmpJ_cmp K H hS Gt j hj y
    rw [h1, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have h2 : trC (hC j hj) (j + 1) ((ex.tw.fm u μ).emb (j + 1) y) =
        (I.at' j hj).M.emb (j + 1) ((I.at' j hj).eps.symm y) := by
      apply trC_heq
      have := (I.at' j hj).eps_emb ((I.at' j hj).eps.symm y)
      rwa [LinearEquiv.apply_symm_apply] at this
    rw [h2]
    exact rdS_cmpJ (iA := Y.algKf) (I.at' j hj).st (ex.cmp.embW u w h) (H.core j hj) hS ι hι _ c' L'
  · rw [dite_eq_right hj]
    have h1 : (kerAtMu_any K H hS Gt Ch hCh).cmp (j + 1) y = 0 := by
      show cmpSJ H hS j y = 0
      unfold cmpSJ
      rw [dite_eq_right hj]
      rfl
    rw [h1]
    simp

end Formalism.L2.KerInert.SecondKernelProjection
end
end
