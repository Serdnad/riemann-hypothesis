module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle168
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle177
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle173
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle174
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle165
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThIndep
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmEmbeddingsEqOneOfInert
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle300
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeAdelicLatticeLocalizationEq
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

theorem bc_reGL_comm {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {m n : ℕ} (e : Fin m ≃ Fin n) (x : GL (Fin m) A) :
    Formalism.UG.bc φ (Formalism.L2.PairingIndexBounds.F.reGL e x) = Formalism.L2.PairingIndexBounds.F.reGL e (Formalism.UG.bc φ x) := by
  apply Units.ext
  ext a b
  rfl

theorem sameOff_reGL_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 F)) {m n : ℕ} (e : Fin m ≃ Fin n) (x y : GL (Fin m) (AfE F E))
    (h : SameOff w x y) : SameOff w (Formalism.L2.PairingIndexBounds.F.reGL e x) (Formalism.L2.PairingIndexBounds.F.reGL e y) := fun w' hw => by
  rw [bc_reGL_comm, bc_reGL_comm, h w' hw]

theorem sameOff_eps_of_bases {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}
    {σ : E →ₐ[F] E} {Jm : Matrix (Fin n) (Fin n) E} {A : LocAt F E n G} (hG : LocGood σ Jm A) (i : G.comp)
    (g g' : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (v : Fin G.P.nV) (hgg : ∀ v', v' ≠ v → g v' = g' v') :
    SameOff (A.pl v).1 (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ UPts σ Jm (FiniteAdeleRing (𝓞 F) F))
      (Classical.epsilon fun x => A.IsPt i g' x ∧ x ∈ UPts σ Jm (FiniteAdeleRing (𝓞 F) F)) := by
  have ha := Classical.epsilon_spec (p := fun x => A.IsPt i g x ∧ x ∈ UPts σ Jm (FiniteAdeleRing (𝓞 F) F))
    ⟨_, hG.isPt_sec i g, Subgroup.mul_mem _ (hG.yG_mem i) (hG.sec _).2⟩
  have hb := Classical.epsilon_spec (p := fun x => A.IsPt i g' x ∧ x ∈ UPts σ Jm (FiniteAdeleRing (𝓞 F) F))
    ⟨_, hG.isPt_sec i g', Subgroup.mul_mem _ (hG.yG_mem i) (hG.sec _).2⟩
  exact GlobalTheory.TwV.Xc.sameOff_of_isPt F E σ n p G A Jm hG i g g' ⟨_, ha.2⟩ ⟨_, hb.2⟩ ha.1 hb.1 v hgg



theorem sameOff_len_of_sameAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v j (hj : j ≤ D.R.m) (La Lb : (sysS H X std).Lt j), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameOff ((A0 J).pl v).1 (J.pt std j hj La).1 (J.pt std j hj Lb).1 ∧ ∀ v', v' ≠ v → len (sysS H X std) v' j La.2 = len (sysS H X std) v' j Lb.2) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS v j hj La Lb hab
  obtain ⟨hLa, hLb, h1, h2⟩ := hab
  have hent : ∀ v', v' ≠ v → La.2 ((sysS H X std).vJ j v') = Lb.2 ((sysS H X std).vJ j v') := by
    intro v' hv'
    have hne : (sysS H X std).vJ j v' ≠ (sysS H X std).vJ j v := by
      intro h
      apply hv'
      have := congrArg ((sysS H X std).vB j) h
      rwa [Formalism.L2.G.Pend.vB_vJ, Formalism.L2.G.Pend.vB_vJ] at this
    have := congrFun h2 ((sysS H X std).vJ j v')
    exact (Function.update_of_ne hne _ _).symm.trans (this.trans (Function.update_of_ne hne _ _))
  refine ⟨?_, fun v' hv' => by unfold len; rw [hent v' hv']⟩
  have hlat : ∀ v', v' ≠ v → (sysS H X std).latAt v' j La.2 = (sysS H X std).latAt v' j Lb.2 := by
    intro v' hv'
    have := hent v' hv'
    cases j <;> exact this
  obtain ⟨hr, hpa⟩ := (hD j hj La hLa).1
  obtain ⟨hr', hpb⟩ := (hD j hj Lb hLb).1
  rw [hpa, hpb]
  apply sameOff_reGL_of
  obtain ⟨c, a⟩ := La
  obtain ⟨c', b⟩ := Lb
  dsimp only at h1
  subst h1
  cases j with
  | zero =>
    simp only [Joint.cp, cpAt, chAt]
    apply sameOff_reGL_of
    apply sameOff_eps_of_bases J.one.good
    intro v' hv'
    have hl := hlat v' hv'
    dsimp only at hl
    unfold basesAt
    rw [hl]
  | succ i =>
    simp only [Joint.cp, cpAt]
    simp only [chAt, dif_pos hj]
    apply sameOff_reGL_of
    rw [show (A0 J).pl v = ((I.at' i hj).st.loc ((I.at' i hj).st.eC.symm c).1).pl v from (J.pl i hj _ v).symm]
    apply sameOff_eps_of_bases (H.core i hj _).good
    intro v' hv'
    have hl := hlat v' hv'
    dsimp only at hl
    unfold basesAt
    rw [hl]

end GlobalTheory.TwV.Xc
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc



theorem chart_places_firstFactor_eq_zero :
    Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
      ∀ j (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) v, ((I.at' j hj).st.loc β).pl v = (A0 J).pl v ∧
        ∀ x, phiA ((I.at' j hj).st.loc β) v x = phiA (A0 J) v x) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hD _hS j hj β v
  refine ⟨J.pl j hj β v, ?_⟩
  have h := firstFactor_agree D.host.F D.host.E _ _ (((I.at' j hj).st.loc β).pl v).1 ((A0 J).pl v).1
    (((I.at' j hj).st.loc β).eQ v) ((A0 J).eQ v) (((I.at' j hj).st.loc β).ph v) ((A0 J).ph v)
    (fun c => by
      show ((((I.at' j hj).st.loc β).spl v) ((1 : D.host.E) ⊗ₜ[D.host.F] c)).1 = c
      rw [J.alg j hj β v c])
    (fun c => by
      show (((A0 J).spl v) ((1 : D.host.E) ⊗ₜ[D.host.F] c)).1 = c
      rw [J.alg0 v c])
    ((H.core j hj β).int v) (J.one.int v)
    (fun a => by
      have h1 := RingHom.congr_fun (J.iw j hj β v) a
      exact h1)
  exact h.2

end GlobalTheory.TwV.Xc
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section



theorem GlobalTheory.TwV.Xc.kapG_at_site : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → FillAt (hT := hT) (H := H) (X := X) std j hj → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) ∈ TaylorLogMetric.Qbar ∧ kapG (sysS H X std) ℂ_[D.what₂.places.resChar w] j c γ = TaylorLogMetric.lamC S.lam (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) * ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hSpl hPos j hj c La γ g κ hr hLat hMove hFill
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  obtain ⟨hgU, -, hfr, r, hr1, hr2⟩ := hMove

  obtain ⟨-, hE⟩ := eMat_unitary_det D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) (fun x => rfl) _ _ hr
    (gramN D j hj.le) (J.A.crd j hj.le) (J.pins.crd_orth j hj.le)
  obtain ⟨hEu, hEdet⟩ := hE g hgU
  have ha : g.1.det * D.host.conj g.1.det = 1 := by
    have h1 := congrArg Matrix.det hEu
    rw [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one, hEdet] at h1
    rw [← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj D]
    exact h1

  have hdet : ∀ v, (gamAt (sysS H X std) j c γ v : Matrix (Fin (((sysS H X std).Pj j).m + 1)) (Fin (((sysS H X std).Pj j).m + 1)) ((sysS H X std).G.P.Qq v)).det = J.rho std v g.1.det := by
    intro v
    have h1 := congrArg Matrix.det (hfr hr v)
    have hm : ((eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g).map (J.rho std v)).det = J.rho std v g.1.det := by
      rw [← hEdet]; exact (RingHom.map_det (J.rho std v) _).symm
    rw [Matrix.det_mul, Matrix.det_mul, hm] at h1
    have hu : IsUnit ((J.fd std).frM j (c, La) v).det := isUnit_det_frameMatrix_ofCharts _ _ _ j (c, La) v
    rw [mul_comm (J.rho std v _)] at h1
    exact hu.mul_left_cancel h1
  have ha0 : g.1.det ≠ 0 := fun h0 => by rw [h0, zero_mul] at ha; exact zero_ne_one ha
  have hT0 : ∀ τ, TaylorLogMetric.embT D τ g.1.det ≠ 0 := fun τ => (map_ne_zero _).2 ha0
  have hkap := kapG_eq_char_inf D (D.what₂.places.resChar w) (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) S.lam (J.rho std) hPos j c γ
    g.1.det ha hdet

  obtain ⟨e, he, hmu⟩ := S.law.mu_rat j hj
  have hdetR : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g) = ratId D.host.F D.host.E (Matrix.GeneralLinearGroup.det g) := by
    ext
    simp [GlobalTheory.TwU.ratA, ratId, Formalism.UG.bc, RingHom.map_det]
  have hmuT : S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) = ∏ τ, TaylorLogMetric.embT D τ g.1.det ^ e τ := by
    rw [hdetR, hmu _ (by simpa using ha)]
    simp
  have hq1 : (∏ τ, TaylorLogMetric.embT D τ g.1.det ^ e τ) ∈ TaylorLogMetric.Qbar :=
    prod_mem fun τ _ => zpow_mem (embT_mem_qbar D τ _) _
  have hz : D.what₂.embLL r ∈ algebraicClosure ℚ ℂ := by
    rw [mem_algebraicClosure_iff']
    exact (Algebra.IsIntegral.isIntegral r).map D.what₂.embLL.toRatAlgHom
  have hχ : S.E.toCEmb.iK (algebraMap (sysS H X std).G.O (sysS H X std).G.Kf ((((sysS H X std).Lv.lev j c).χ γ : (sysS H X std).G.Oˣ) : (sysS H X std).G.O)) =
      TaylorLogMetric.lamC S.lam (D.what₂.embLL r) := by
    rw [hr2, S.hK r hz]
    exact (lamC_qbar S.lam ⟨_, hz⟩).symm

  set A : ℤ := (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)) with hA
  set B : ℤ := (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ) with hB
  have hfill := hFill e he
  have hq2 : (∏ τ, TaylorLogMetric.embT D τ g.1.det) ^ (-A - B) ∈ TaylorLogMetric.Qbar :=
    zpow_mem (prod_mem fun τ _ => embT_mem_qbar D τ _) _
  have hkey : (∏ v : (sysS H X std).Pl, ∏ s : Fin ((sysS H X std).G.P.n' v), TaylorLogMetric.embT D (hT.gat_pos u w hg ⟨v, s⟩) g.1.det ^ (sysS H X std).w v (j + 1) s) =
      (∏ τ, TaylorLogMetric.embT D τ g.1.det ^ e τ) * (∏ τ, TaylorLogMetric.embT D τ g.1.det) ^ (-A - B) := by
    simp_rw [hfill]
    rw [← Fintype.prod_sigma (fun x => TaylorLogMetric.embT D (hT.gat_pos u w hg x) g.1.det ^ (e (hT.gat_pos u w hg x) - A - B))]
    rw [Fintype.prod_equiv (hT.gat_pos u w hg) _ (fun τ => TaylorLogMetric.embT D τ g.1.det ^ (e τ - A - B)) (fun _ => rfl)]
    rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← zpow_add₀ (hT0 τ)]
    ring_nf
  have hlen : ∀ v, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La) =
      -((sysS H X std).vm v (j + 1) * ordP ((sysS H X std).G.P.W v) (D.what₂.places.resChar w) (J.rho std v g.1.det)) := by
    intro v
    rw [len_smul_tup _ (sysS H X std) j c γ La hLat v, hdet v]
    ring
  refine ⟨hmuT ▸ hq1, ?_⟩
  rw [hkap, hχ, hkey, hmuT, ← hr1, Finset.sum_congr rfl fun v _ => hlen v, Finset.sum_neg_distrib,
    show -A - B = -(A + B) by ring, mul_assoc (D.what₂.embLL r), Formalism.L2.Ker.lamC_mul S.lam hz (mul_mem hq1 (by rw [show -(A + B) = -A - B by ring]; exact hq2))]

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.SBad

theorem not_both_mem {R : Type*} [CommRing R] {I : Ideal R} (hI : I ≠ ⊤) {a b : ℕ} (h : Nat.Coprime a b)
    (ha : (a : R) ∈ I) (hb : (b : R) ∈ I) : False := by
  obtain ⟨s, r, hsr⟩ := h.cast (R := R)
  exact hI ((Ideal.eq_top_iff_one _).2 (hsr ▸ I.add_mem (I.mul_mem_left _ ha) (I.mul_mem_left _ hb)))

theorem mem_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A}
    (h : P ∈ Formalism.L2.Col.divs a) : a ∈ P.asIdeal := by
  unfold Formalism.L2.Col.divs at h
  split_ifs at h with hf
  · simpa using h
  · simp at h

theorem coprime_absNorm_of_notMem {E : Type} [Field E] [NumberField E] (p : ℕ) [Fact p.Prime]
    (P : HeightOneSpectrum (𝓞 E)) (h : ((p : ℕ) : 𝓞 E) ∉ P.asIdeal) : Nat.Coprime (Ideal.absNorm P.asIdeal) p := by
  refine GlobalTheory.NormUnitInert.Arith.coprime_absNorm p P.ne_bot ?_
  refine P.isMaximal.out.2 _ (lt_of_le_of_ne le_sup_left fun he => h ?_)
  rw [he]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

theorem notMem_Sall (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (p : ℕ) (hp : p.Prime)
    (hTp : Nat.Coprime (D.mem u).A.T p) (hgp : ∀ i, p ≠ D.host.g i) (hQ : p ∉ Dx.Qp μ)
    (P : HeightOneSpectrum (𝓞 t.X.E)) (hP : P ∈ Formalism.L2.Col.Sall t.sel (t.tup μ) (t.word u)) :
    ((p : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal := by
  intro hpP
  simp only [Formalism.L2.Col.Sall, Formalism.L2.Col.rowSG, Formalism.L2.Col.uSG, Formalism.L2.Col.Primes.vGs, Finset.mem_union] at hP
  have hG : ∀ i, P ∈ t.Pr.vG i → False := fun i hPi => by
    have hc := mem_of_mem_divs hPi
    have hgm : ((D.host.g i : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← t.g_rec i, ← t.pr_ok.piG_norm]
      exact Ideal.mul_mem_left _ _ hc
    have hgi : (D.host.g i).Prime := t.g_rec i ▸ t.pr_ok.g_prime i
    exact not_both_mem P.isPrime.ne_top ((Nat.coprime_primes hgi hp).2 (hgp i).symm) hgm hpP
  rcases hP with hP | (hP | hP) | hP
  · have hpi := mem_of_mem_divs hP
    have hTm : (((D.mem u).A.T : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← t.T_rec u, ← t.pr_ok.piT_norm]
      exact Ideal.mul_mem_right _ _ hpi
    exact not_both_mem P.isPrime.ne_top hTp hTm hpP
  · exact hG 0 hP
  · exact hG 1 hP
  · exact hQ ((t.Q_rec μ p).2 ⟨hp, P, hP, hpP⟩)



theorem bad_prime_to_p : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => Nat.Coprime (t.rd u μ).lev (D.what₂.places.resChar w) ∧ (∀ Q ∈ GlobalTheory.TwU.ssRec t u μ, (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ (∀ v ∈ Formalism.L2.Col.plUnder D.host.F (GlobalTheory.TwU.ssRec t u μ), (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) ∧ ∀ v, GlobalTheory.TwU.UnderSB t μ v → (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X hF std t J S _ _
  classical
  have hp : (D.what₂.places.resChar w).Prime := hF.out
  obtain ⟨-, -, hTp, hgp⟩ := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  have hSS := (t.rd_chain u μ).1
  have hlev := (t.rd_chain u μ).2.1
  have key := fun P hP => notMem_Sall t u μ _ hp hTp hgp J.away P hP
  have keyE : ∀ Q ∈ GlobalTheory.TwU.ssRec t u μ, (((D.what₂.places.resChar w : ℕ)) : 𝓞 D.host.E) ∉ Q.asIdeal := by
    intro Q hQ hm
    obtain ⟨P, hP, rfl⟩ := Finset.mem_map.1 hQ
    refine key P (hSS ▸ hP) ((GlobalTheory.TwU.mem_seamP t.seam P _).1 ?_)
    rw [map_natCast]
    exact hm
  have keyF : ∀ v ∈ Formalism.L2.Col.plUnder D.host.F (GlobalTheory.TwU.ssRec t u μ),
      (((D.what₂.places.resChar w : ℕ)) : 𝓞 D.host.F) ∉ v.asIdeal := by
    rintro v ⟨Q, hQ, hv⟩ hm
    rw [hv, Ideal.mem_comap, map_natCast] at hm
    exact keyE Q hQ hm
  refine ⟨?_, keyE, keyF, ?_⟩
  · rw [hlev]
    have hq : ∀ P : Formalism.L2.Col.rowSG t.Pr t.sel (t.tup μ), Nat.Coprime (Formalism.L2.Col.qOf P.1) (D.what₂.places.resChar w) :=
      fun P => coprime_absNorm_of_notMem _ P.1 (key P.1 (Finset.mem_union_right _ P.2))
    have hprod : Nat.Coprime (∏ P : Formalism.L2.Col.rowSG t.Pr t.sel (t.tup μ), Formalism.L2.Col.qOf P.1) (D.what₂.places.resChar w) :=
      Nat.Coprime.prod_left fun P _ => hq P
    have hT' : Nat.Coprime (t.Pr.T (t.word u)) (D.what₂.places.resChar w) := by rw [t.T_rec u]; exact hTp
    simp only [Formalism.L2.Ker.levC, Formalism.L2.Col.cAof, Formalism.L2.Col.cBof]
    exact Nat.Coprime.mul_left (Nat.Coprime.pow_left _ hprod) (Nat.Coprime.mul_left hT' (Nat.Coprime.pow_left _ hprod))
  · rintro v ⟨P, hP, hv⟩ hm
    rw [hv, Ideal.mem_comap, map_natCast] at hm
    refine key P (Finset.mem_union_right _ hP) ((GlobalTheory.TwU.mem_seamP t.seam P _).1 ?_)
    rw [map_natCast]
    exact hm

end GlobalTheory.TwV.Xc.SBad

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.Mv0

theorem frm_gen {E Q : Type} [Field E] [Field Q] (σ : E →+* E) {a N : ℕ} (rk hr : a = N) (J0 : Matrix (Fin N) (Fin N) E)
    (B g : GL (Fin N) E) (iw : E →+* Q) (M : GL (Fin a) Q) (hM : castGL rk Q M = bc iw (B⁻¹ * g * B)) :
    (((LinearMap.toMatrix' ((stdCo σ (J0.reindex (finCongr rk.symm) (finCongr rk.symm)) : (Fin a → E) ≃ₗ[E] (Fin a → E)) :
      (Fin a → E) →ₗ[E] (Fin a → E))) * ((reGL (finCongr rk.symm) B : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)).map iw).submatrix
        (finCongr (rfl : a = a)) (finCongr (rfl : a = a)) * (M : Matrix (Fin a) (Fin a) Q) =
    (eMat hr σ J0 g).map iw *
      ((((LinearMap.toMatrix' ((stdCo σ (J0.reindex (finCongr rk.symm) (finCongr rk.symm)) : (Fin a → E) ≃ₗ[E] (Fin a → E)) :
      (Fin a → E) →ₗ[E] (Fin a → E))) * ((reGL (finCongr rk.symm) B : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)).map iw).submatrix
        (finCongr (rfl : a = a)) (finCongr (rfl : a = a))) := by
  subst rk
  have hJ : J0.reindex (finCongr (rfl : a = a)) (finCongr (rfl : a = a)) = J0 := by ext i j; simp
  have hB : ((reGL (finCongr (rfl : a = a)) B : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) = (B : Matrix (Fin a) (Fin a) E) := by
    ext i j
    show (Matrix.reindexAlgEquiv E E (finCongr (rfl : a = a)) (B : Matrix (Fin a) (Fin a) E)) i j = _
    simp [Matrix.reindexAlgEquiv_apply]
  have hMm : (M : Matrix (Fin a) (Fin a) Q) = ((B⁻¹ * g * B : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).map iw := by
    ext i j
    have h1 := congrArg (fun x : GL (Fin a) Q => (x : Matrix (Fin a) (Fin a) Q) i j) hM
    simp only [castGL_apply] at h1
    exact h1
  have hE : eMat hr σ J0 g = LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) *
      (g : Matrix (Fin a) (Fin a) E) *
      LinearMap.toMatrix' (((stdCo σ J0).symm : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) := by
    have e0 : eMat hr σ J0 g = LinearMap.toMatrix' (stdG σ J0 g).toLinearMap := by ext i j; simp [eMat]
    rw [e0]
    have e1 : (stdG σ J0 g).toLinearMap = (stdCo σ J0 : (Fin a → E) →ₗ[E] (Fin a → E)) ∘ₗ (Matrix.toLin' (g : Matrix (Fin a) (Fin a) E)) ∘ₗ
        ((stdCo σ J0).symm : (Fin a → E) →ₗ[E] (Fin a → E)) := by
      apply LinearMap.ext; intro x; rfl
    rw [e1, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', Matrix.mul_assoc]
  have hsub : ∀ A : Matrix (Fin a) (Fin a) Q, A.submatrix (finCongr (rfl : a = a)) (finCongr (rfl : a = a)) = A := fun A => by ext i j; rfl
  rw [hsub, hJ, hB, hMm, hE, ← Matrix.map_mul, ← Matrix.map_mul]
  congr 1
  have hci : LinearMap.toMatrix' (((stdCo σ J0).symm : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) *
      LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
  have hBB : (B : Matrix (Fin a) (Fin a) E) * ((B⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul]
  calc _ = LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) *
        ((B : Matrix (Fin a) (Fin a) E) * ((B⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)) * (g : Matrix (Fin a) (Fin a) E) * (B : Matrix (Fin a) (Fin a) E) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by
          rw [hBB, Matrix.mul_one]
          calc _ = LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) * (g : Matrix (Fin a) (Fin a) E) *
                (LinearMap.toMatrix' (((stdCo σ J0).symm : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) *
                  LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E))) * (B : Matrix (Fin a) (Fin a) E) := by
                rw [hci, Matrix.mul_one]
            _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.TwV.Xc.Mv0

namespace GlobalTheory.TwV.Xc.Mv0

open Formalism.MainNotions.G.CmpJ.PStabEq

theorem regl2 {R : Type} [CommRing R] {a N : ℕ} (h : a = N) (h' : N = a) (y : GL (Fin N) R) :
    Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h') y) = y := by
  subst h
  ext i j
  show (Matrix.reindexAlgEquiv R R (finCongr (rfl : a = a)) (Matrix.reindexAlgEquiv R R (finCongr h') (y : Matrix (Fin a) (Fin a) R))) i j = _
  simp [Matrix.reindexAlgEquiv_apply]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n p : ℕ} {G : GAtP p}
  {A : LocAt F E n G} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {S : StepLevel F E σ J T f bad}
  {cl : Type} {y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F)}

theorem ptEps_spec (H1 : OneHyp S A y) (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
    A.IsPt i g (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) ∧
      (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨c, γ₀, κ₀, hγ₀, hp⟩ := ptEx_of H1.good S y H1.y_bij.2 i g
  exact Classical.epsilon_spec (p := fun x => A.IsPt i g x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    ⟨_, hp, Subgroup.mul_mem _ (Subgroup.mul_mem _ (bc_mem hγ₀) (y c).2) (U_le κ₀.2)⟩

theorem pt_gen (H1 : OneHyp S A y) (i : G.comp) (γ : (G.lev i).Γ) (L : G.P.Tup) (hL : G.P.IsLatTup L) (κa : S.U)
    (hκa : A.IsAway i γ κa.1) (bas : G.P.Tup → ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hbas : ∀ L' v, bas L' v = Classical.epsilon fun g : GL (Fin (G.P.m + 1)) (G.P.Qq v) =>
      L' v = colSpan (G.P.W v) (g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) :
    ∃ κ : S.U, (Classical.epsilon fun x => A.IsPt i (bas ((G.lev i).smul γ L)) x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) =
      GlobalTheory.TwU.ratA F (A.gamI i γ) * (Classical.epsilon fun x => A.IsPt i (bas L) x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) * κ.1 ∧
      S.chi κ * S.chi κa = 1 := by
  obtain ⟨g0, hg0⟩ := exists_bases1 L hL
  have hb : ∀ (L' : G.P.Tup) (g1 : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)),
      (∀ v, L' v = colSpan (G.P.W v) (g1 v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
      ∀ v, L' v = colSpan (G.P.W v) (bas L' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := by
    intro L' g1 h v
    rw [hbas]
    exact Classical.epsilon_spec (p := fun g : GL (Fin (G.P.m + 1)) (G.P.Qq v) =>
      L' v = colSpan (G.P.W v) (g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) ⟨g1 v, h v⟩
  have hbL := hb L g0 hg0
  have hbγ := hb _ _ (smul_colSpan i γ L g0 hg0)
  have hs := ptEps_spec H1 i (bas L)
  have hs' := ptEps_spec H1 i (bas ((G.lev i).smul γ L))
  exact GlobalTheory.TwV.Xc.isPt_move_eq F E σ n p G A J T f bad S H1.good H1.int H1.hypP H1.actB H1.bad_p i γ (H1.gamU i γ) κa hκa
    (bas L) (bas ((G.lev i).smul γ L)) (fun v => (hbγ v).symm.trans (smul_colSpan i γ L (bas L) hbL v))
    ⟨_, hs.2⟩ ⟨_, hs'.2⟩ hs.1 hs'.1

end GlobalTheory.TwV.Xc.Mv0

namespace GlobalTheory.TwV.Xc



theorem moveBy_zero : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (c : (sysS H X std).Lv.comp 0) (La : ((sysS H X std).Pj 0).Tup) (γ : ((sysS H X std).Lv.lev 0 c).Γ), ((sysS H X std).Pj 0).IsLatTup La → ∃ g κ, MoveBy std J 0 (Nat.zero_le _) c La γ g κ) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS c La γ hL
  have hfr : ∀ (hr : ((sysS H X std).Pj 0).m + 1 = D.R.N 0) (v : (sysS H X std).Pl),
      (J.fd std).frM 0 (c, La) v * (gamAt (sysS H X std) 0 c γ v : Matrix _ _ _) =
        (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ((A0 J).gamI c γ)).map (J.rho std v) * (J.fd std).frM 0 (c, La) v := by
    intro hr v
    exact Mv0.frm_gen _ (A0 J).rk hr (gramN D 0 (Nat.zero_le _)) (A0 J).B ((A0 J).gamI c γ) ((A0 J).iw v) _ (J.one.actB c v γ)
  obtain ⟨κa, hκa⟩ := awayEx_of J.one.good _ J.one.gam c γ
  obtain ⟨ra, hra1, hra2⟩ := (lev0AtOf_compatible J.Gd.cmp u w hg).chi c γ κa hκa
  have hJpt : ∀ L', (J.pt std 0 (Nat.zero_le _) (c, L')).1 = Classical.epsilon fun x => (A0 J).IsPt c (basesAt _ std _ _ _ _ _ _ _ 0 L') x ∧
      x ∈ UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    intro L'
    have hs := Mv0.ptEps_spec J.one c (basesAt _ std _ _ _ _ _ _ _ 0 L')
    have hspec : J.IsPt std 0 (Nat.zero_le _) (c, L') (J.pt std 0 (Nat.zero_le _) (c, L')) :=
      Classical.epsilon_spec (p := J.IsPt std 0 (Nat.zero_le _) (c, L')) ⟨⟨_, hs.2⟩, (A0 J).rk, (Mv0.regl2 _ _ _).symm⟩
    obtain ⟨hr, e⟩ := hspec
    rw [e]
    exact Mv0.regl2 _ _ _
  obtain ⟨κ, hκ1, hκ2⟩ := Mv0.pt_gen J.one c γ La hL κa hκa (basesAt _ std _ _ _ _ _ _ _ 0) (fun L' v => rfl)
  obtain ⟨-, -, hU, hchi⟩ := J.lev0 (J.chart std 0 (Nat.zero_le _) (c, La))
  have hmem : κ.1 ∈ ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) (c, La))).lev.U := by rw [hU]; exact κ.2
  refine ⟨(A0 J).gamI c γ, ⟨κ.1, hmem⟩, J.one.gamU c γ, ?_, hfr, ra⁻¹, ?_, ?_⟩
  · exact (hJpt _).trans (hκ1.trans (by rw [hJpt]))
  · rw [hchi ⟨κ.1, hmem⟩ κ rfl, map_inv₀, hra1, ← Units.val_inv_eq_inv_val]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) (eq_inv_of_mul_eq_one_left hκ2).symm
  · rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left hra2

end GlobalTheory.TwV.Xc

end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.companionLattice_adelicLattice_localization_eq : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (σ : E →ₐ[F] E), (σ : E →+* E) = sp.cm.sig → ∀ (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (a : 𝓞 E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (P : HeightOneSpectrum (𝓞 E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (compan (sp := sp) J a (latAd x Lb)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd x (compan (sp := sp) J a Lb)) := by
  first | exact @GlobalTheory.CompanLatAd.locP_companion_latAd | exact GlobalTheory.CompanLatAd.locP_companion_latAd | (intros; apply GlobalTheory.CompanLatAd.locP_companion_latAd <;> assumption)
end
