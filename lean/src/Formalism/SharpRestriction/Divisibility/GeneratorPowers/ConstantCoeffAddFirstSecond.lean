import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffAddSecondThird
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.MulGenScaleRight
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSTrunc

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix ReciprocityTheory.ChartRestriction.G.TB Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing (ev_ev ev_X hasSubst_pts exp_add subst_exp exp_zero)

section Series

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

theorem formal_log_add_first_two (G : FGLaw S d) (l : Fin d) :
    ev (n := 3) ![G.add (pt S d 0) (pt S d 1)] (LogPf.logOf G l) =
      ev (n := 3) ![pt S d 0] (LogPf.logOf G l) + ev (n := 3) ![pt S d 1] (LogPf.logOf G l) := by
  exact formal_log_add_points G _ _ (cc_pt' 0) (cc_pt' 1) l

theorem constantCoeff_add_first_second (G : FGLaw S d) (i : Fin d) :
    MvPowerSeries.constantCoeff (G.add (pt S (n := 3) d 0) (pt S d 1) i) = 0 :=
  constantCoeff_add_points G _ _ (cc_pt' 0) (cc_pt' 1) i

theorem twist_mul_first_argument (G : FGLaw S d) (cc : Fin d → Fin d → S) :
    ev (n := 3) ![G.add (pt S d 0) (pt S d 1), pt S d 2] (expP (-bilL G cc)) =
      ev (n := 3) ![pt S d 0, pt S d 2] (expP (-bilL G cc)) * ev (n := 3) ![pt S d 1, pt S d 2] (expP (-bilL G cc)) := by
  exact twist_mul_first_points G cc _ _ _ (cc_pt' 0) (cc_pt' 1) (cc_pt' 2)

theorem twist_sym (G : FGLaw S d) (cc : Fin d → Fin d → S) (hs : ∀ i l, cc i l = cc l i) :
    ev (n := 2) ![pt S d 1, pt S d 0] (expP (-bilL G cc)) = expP (-bilL G cc) := by
  have ha : ∀ j i, MvPowerSeries.constantCoeff ((![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) j i) = 0 :=
    pair_property (fun f : PS S 2 d => MvPowerSeries.constantCoeff f = 0)
      (u := pt S d 1) (v := pt S d 0) (cc_pt' 1) (cc_pt' 0)
  have hsw : ev (n := 2) ![pt S d 1, pt S d 0] (bilL G cc) = bilL G cc := by
    rw [ev_bilL G cc _ ha]
    conv_rhs => rw [bilL]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hs l i, mul_comm] <;> rfl
  rw [ev_expP _ ha, hsw]

theorem bilL_add (G : FGLaw S d) (c c' : Fin d → Fin d → S) : bilL G (c + c') = bilL G c + bilL G c' := by
  simp only [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem bilL_zero (G : FGLaw S d) : bilL G 0 = 0 := by
  simp [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL]

theorem twist_add (G : FGLaw S d) (c c' : Fin d → Fin d → S) :
    expP (-bilL G (c + c')) = expP (-bilL G c) * expP (-bilL G c') := by
  rw [bilL_add, neg_add]
  exact exp_add (by rw [map_neg, cc_bilL, neg_zero]) (by rw [map_neg, cc_bilL, neg_zero])

theorem twist_zero (G : FGLaw S d) : expP (-bilL G 0) = 1 := by
  rw [bilL_zero, neg_zero]
  exact exp_zero

end Series

section Jet

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

theorem twist_mul_first_argument_jet (G : FGLaw S d) (cc : Fin d → Fin d → S) (m : ℕ) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m ![0, 1] (G.F j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) =
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) *
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) := by
  have hX (k : Fin 3) := standard_point_jet (S := S) (d := d) m k
  rw [jetSubstP_pair m (add_point_jet G m 0 1) (hX 2),
    jetSubstP_pair m (hX 0) (hX 2), jetSubstP_pair m (hX 1) (hX 2),
    twist_mul_first_argument, FBIdJet.psJet_mul]

theorem twist_sym_jet (G : FGLaw S d) (cc : Fin d → Fin d → S) (hs : ∀ i l, cc i l = cc l i) (m : ℕ) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) =
      psJet m (expP (-bilL G cc)) := by
  have hX (k : Fin 2) := standard_point_jet (S := S) (d := d) m k
  rw [jetSubstP_pair m (hX 1) (hX 0), twist_sym G cc hs]

def twU (G : FGLaw S d) (c : Fin d → Fin d → S) (m : ℕ) : (Jet S (Fin 2 × Fin d) m)ˣ where
  val := psJet m (expP (-bilL G c))
  inv := psJet m (expP (-bilL G (-c)))
  val_inv := by rw [← FBIdJet.psJet_mul, ← twist_add, add_neg_cancel, twist_zero, FBIdJet.psJet_one]
  inv_val := by rw [← FBIdJet.psJet_mul, ← twist_add, neg_add_cancel, twist_zero, FBIdJet.psJet_one]

theorem twU_val (G : FGLaw S d) (c : Fin d → Fin d → S) (m : ℕ) :
    (twU G c m : Jet S (Fin 2 × Fin d) m) = psJet m (expP (-bilL G c)) := rfl

end Jet

section Chart

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S)

theorem fixTw [StarRing (𝓞 E)] (C : ChartAt Xo c y) (cc : ℕ → Fin C.d → Fin C.d → S) (h0 : cc 0 = 0)
    (hsym : ∀ m i j, cc m i j = cc m j i)
    (hbal : ∀ m (a : 𝓞 E), Matrix.transpose (dLin (C.B.A.act a)) * Matrix.of (cc m) =
      Matrix.of (cc m) * dLin (C.B.A.act (H.bar a)))
    (hstep : ∀ m, ∃ U : (Jet S (Fin 2 × Fin C.d) m)ˣ,
      (U : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m - cc (m + 1)))) ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (C.e (m + 1))
          (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)).left)
        (scaleGen _ _ (unitΓ U) (C.e m))) :
    ∃ (e' : ∀ m, FrTy y C.d C.x m) (hfr : IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e')
      (hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1)),
      FrTruncC y { C with e := e', frame := hfr, rig0 := hrig } ∧
      ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
        (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m))) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m)) := by
  choose U hU hc using hstep
  let T : ∀ m, (Jet S (Fin 2 × Fin C.d) m)ˣ := fun m => twU C.B.G (cc m) m
  have hm1 : ∀ m, sub C.d m ![fun j => psIn C.d m ![0, 1] (C.B.G.F j), fun j => X ((2 : Fin 3), j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) *
        sub C.d m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) := fun m =>
    Units.ext (by rw [Units.val_mul]; exact twist_mul_first_argument_jet C.B.G (cc m) m)
  have hm2 : ∀ m, sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => psIn C.d m ![1, 2] (C.B.G.F j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)] (T m) *
        sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) := fun m =>
    Units.ext (by rw [Units.val_mul]; exact twist_mul_second_argument_jet C.B.G (cc m) m)
  have hs : ∀ m, sub C.d m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] (T m) = T m := fun m =>
    Units.ext (twist_sym_jet C.B.G (cc m) (hsym m) m)
  have hb : ∀ m a, sub C.d m ![fun j => psIn C.d m ![0] (C.B.A.act a j), fun j => X ((1 : Fin 2), j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a) j)] (T m) :=
    fun m a => Units.ext (twist_bal_jet C.B (cc m) a (H.bar a) (hbal m a) m)
  have hT : ∀ m, Units.map (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m).toMonoidHom
      (T (m + 1)) * U m = T m := fun m => Units.ext (by
    rw [Units.val_mul, Units.coe_map, hU m]
    show (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)
      (psJet (m + 1) (expP (-bilL C.B.G (cc (m + 1))))) * _ = psJet m (expP (-bilL C.B.G (cc m)))
    rw [ExpGB.jetTrunc_psJet, ← FBIdJet.psJet_mul, ← twist_add, add_sub_cancel])
  have hT0 : T 0 = 1 := Units.ext (by
    show psJet 0 (expP (-bilL C.B.G (cc 0))) = 1
    rw [h0, twist_zero, FBIdJet.psJet_one])
  obtain ⟨e', hfr, hrig, htr, hcorr⟩ := fixTw_of y C T U hm1 hm2 hs hb hc hT hT0
  exact ⟨e', hfr, hrig, htr, fun m => ⟨T m, twU_val _ _ _, hcorr m⟩⟩

end Chart

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
