resolve2 := proc(f,g)
  local Vsf, Vsg, LV, LCf, LCg, cf, cg, tf, tg, df, dg;
  Vsf := VarL(f);
  Vsg := VarL(g);
  # leading Var
  if  Vsf[1] <>  Vsg[1] then 
    lprint("Different leading Vars",Vsf[1], Vsg[1]); 
    return NULL 
  else
    LV :=  Vsf[1];
  fi;
  # assuming Simpl(a, [V1]) is already done;
  # coeficciens and terms
  try
    cf := coeffs(f, LV, tf);
  catch "invalid arguments to coeffs":
     lprint("f not polynomial?", LV, f);
     return NULL;
  end try;
  try
    cg := coeffs(g, LV, tg);
  catch "invalid arguments to coeffs":
     lprint("g not polynomial?", LV, g);
      return NULL;
  end try;
  #if tf[1] = tg[1] then
  #  # polynomials of the same order
  #  LCf := collect(cf[1], Vf, simpl, distributed);
  #  LCg := collect(cg[1], Vg, simpl, distributed);
  #  return simpl(LCg*f - LCf*g);
  #else
    df := degree(tf[1], LV);
    dg := degree(tg[1], LV);
    LCf := collect(cf[1], Vf, simpl, distributed);
    LCg := collect(cg[1], Vg, simpl, distributed);    
    if df >= dg then
       `resolve2/rem`(f, g, LCf, LCg, df, dg, LV, Vsg)
    else
       `resolve2/rem`(g, f, LCg, LCg, dg, df, LV, Vsf)
    fi; 
  #fi;
end:


`resolve2/rem` := proc (f, g, LCf, LCg, df::integer, dg::integer, LV, Vs::list, $)
  local K;
  K := LCg^(df-dg+1);
  simpl(frontend(rem, [K*f, g, LV]))
end:

#`resolve2/rem` := proc (f, g, LCf, LCg, df::integer, dg::integer, LV, Vs::list, $)
#  if type(LCg, 'nonzero') then
#    frontend(rem, [f, g, LV]);
#  else
#    lprint("`resolve2/rem` failed for ", LV, "nonzero coeff is", LCg);
#    `resolve/fails/collect`('remainder', 'procname', [f,g], LV, Vs, LCg, [df, dg]);
#  fi;
#end:




##################


