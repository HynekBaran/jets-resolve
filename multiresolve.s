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


# resolve failure table

`resolve/fails/table` := `resolve/fails/clear`(): # global

`resolve/fails/table/counter` := NewIntSeq():

`resolve/fails/clear` := proc()
  global `resolve/fails/table`, `resolve/fails/table/counter`;
  `resolve/fails/table` := table();
  `resolve/fails/table/counter`('set'=0);
end:

`resolve/fails/collect` := proc(kind::symbol, source::uneval, exp, LV, Vs::list, LC, deg::integer, {solvable::truefalse:=NULL}, $)
  global RESOLVE, `resolve/fails/table`, `resolve/fails/table/counter`;
  local i ;
  i := `resolve/fails/table/counter`();
  # backward compatibility
  if kind='linear' then
    RESOLVE := [op(RESOLVE), [LC, LV, -(exp-LC*LV)]]
  elif kind='nonlinear' then
    RESOLVE := [op(RESOLVE), [exp, LV]]
  fi;
  # central fail storage
  `resolve/fails/table`[i] := table([
        ':-kind' = kind, 
        ':-source' = 'source', 
        ':-exp' = exp, 
        ':-LV' = LV, 
        ':-Vs' = Vs, 
        ':-LC' = LC, 
        ':-deg' = deg,
        ':-solvable' = solvable]);
end:

`resolve/fails/print/1` := proc(i)
  global `resolve/fails/table`;
  local T, kind, tail, slv;
  T := `resolve/fails/table`[op(i)];
  kind := T[':-kind'];
  slv := `if`(T['solvable']=true, "solvable", "");
  tprint(sprintf("%a. %s %a solving failed in %a", 
                  op(i), slv, kind, T['LV']),
         newline=false);
  if kind = 'linear' then
    tail := T['exp'] - T['LC']*T['LV'];
    print (smash(T['LC'])*T['LV'] = -smash(tail));    
  elif kind = 'nonlinear' then
    printf("^%a", T['deg']);
    print(smash(T['exp']));
  elif kind = 'reminder' then
    printf("with polynoms of degrees %a and where the problematic leading coefficient of divisor is", T['deg']);
    print(smash(T['LC']));
  else
    error "Wrong kind %1", kind;
  fi;
end:


`resolve/fails/print` := proc()
  global `resolve/fails/table`;
  local inds := [indices(`resolve/fails/table`)];
  print(KOKOKO, inds, `resolve/fails/table`);
  map(`resolve/fails/print/1`, inds);  
end:

##################
`resolve/lin` := proc(as,vl,{ForceFail::truefalse:=false})
  global maxsize, RESOLVE, `resolve/result/suppressedminsize` := NULL;
  local bs,v,cs,ls,ns,ps,p,q,qs,ans,aux,rs,rt,lb, rat, os, os1;
  local T; # local data table
  lb := `RESOLVE:`; rt := `report/tab`[resolve];
  bs := map(Simpl, as, vl);
  if rt > 1 then report(lb,cat(`resolving `, nops(bs),` eq.`)) fi; 
  bs := remove(proc(a) evalb(a = 0) end, bs);  # remove zero eqs.
  if rt > 1 then report(lb,cat(nops(bs), ` eq. nonzero`)) fi; 
  if bs = {} then RETURN () fi;  # no eq.
  ans := {}; rs := {}; os := {};
  # Correction: rvl removed 12.7.2007
  if ForceFail=true then tprint("Enforced linear failure.") fi;
  if rt > 0 then report(lb,`resolving`, nops(bs), `eqns in `,nops(vl), `unknowns`) fi; 
  `resolve/lin/reduce`(bs, vl);
  for v in vl do # for v running through all Vars in reverse Varordering
    if rt > 4 then report(lb,`resolving with respect to`, v) fi; 
    #`resolve/lin/reduce`(bs, vl); ### called above
    cs := select(has, bs, v);  # cs = subset of bs with v 
    if rt > 2 then report(lb,`resolving`, nops(cs), `equations`, `with respect to`, v, `: `, cs) fi; 
    bs := bs minus cs;  # bs = subset without v
    ### linear?
    ls, ns := selectremove(type, cs, linear(v));  # ls = subset of cs linear in v
    map(proc(a) T[a]['kind'] := 'linear' end, ls);
    map(proc(a) T[a]['kind'] := 'nonlinear' end, ns);
    if ForceFail=true then
      # printf("Enforced linear failure (w. r. to %a).\n", v);
      rs := rs union map(proc(a,v) [a,v] end, cs, v)  # move cs to rs   
    else   
      if rt > 4 then report(lb, nops(ls), `of them linear:`, ls) fi; 
      map(proc(a) T[a]['LC'] := coeff(a,v,1) end, ls);
      ### solvable?
      ps, os1 := selectremove(proc(a,v) type (T[a]['LC'],'nonzero') end, ls, v);
      map(proc(a) T[a]['solvable'] :=  evalb(a in ps) end, ls);
      os := os union os1; # save linear but nonresolvable for future
      if rt > 3 then report(lb, `Solving `, nops(cs),  `eqns w. r. to`,  v, nops(ls), 
                                ` of them linear`, nops(ps), ` of them resolvable.`) fi; 
      if ps <> {} then # if solvable eqs,
        qs := map(Simpl, map(`resolve/lin/1`, ps, v), vl); # solve all ps
        if rt > 4 then report(lb,`available solutions:`, qs) fi; 
        qs := sizesort([op(qs)], size);
        q := op(1,qs);
        if rt > 4 then report(lb,`using solution:`, q) fi; 
        bs := bs union `resolve/lin/reduce`(map(`resolve/subs`, cs, v, q), vl);
        if rt > 4 then report(lb,`back substituted system:`, bs) fi; 
        ans := {v = q} union map(proc(a,v,q) 
                                    op(1,a) = `resolve/subs`(op(2,a), v, q) end, 
                                 ans, v, q)
      else 
        # try to subtract pairs of equations; not implemented yet
        rs := rs union map(proc(a,v) [a,v] end, cs, v)  # move cs to rs
      fi;
    fi;
  od;
  if rt > 0 then report(lb,cat(`solved `, nops(ans), ` eq.`)) fi; 
  if rt > 1 then report(lb,cat(`rejected `, nops(rs), ` eq.`)) fi; 
  if rt > 2 then report(lb,[`sizes: solved:`, op(sort(map(size,[op(ans)]))), `rejected:`, op(sort(map(size,[op(rs)]))), `left `, nops(bs), ` eq.`]) fi;    
  ans := map(Simpl, map(eval,ans), vl);
  
  rs := map(proc(r,vl) [Simpl(op(1,r), vl), op(2,r)] end, rs, vl);
  rs := select(proc(r) evalb(op(1,r) <> 0) end, rs);
  aux := ans;
  ans := select(proc(a) size(a) < maxsize end, ans);
  aux := aux minus ans;
  
  rat := `resolve/nonresrat/test`(os, map(lhs-rhs, ans)); 
    (*
          if rat > 1 then
            # There are some nice but nonresolvable linear eqs
            os := map(proc(a) local e; e := Simpl(lhs(a) - rhs(a), vl); [e, LVar(e)] end, ans);
            RESOLVE := 
              map(`resolve/fail`, rs, `A linear resolving failed for`)
              union
              map(`resolve/fail`, os, `B linear resolving omitted for`);
            return FAIL;  
          fi;
          if ans = {} then
            if aux <> {} then lprint(`There are`, nops(aux),`suppressed solutions of sizes:`, op(map(size,aux)));
                `resolve/result/suppressedminsize` := min(op(map(size,aux))); # HB
            else
               `resolve/result/suppressedminsize` := NULL : # HB
            fi;
            RESOLVE := map(`resolve/fail`, rs, `C linear resolving failed for`); # HB
            FAIL
          else op(ans)
          fi;
  *)
  
  lprint(nops(ans), nops(aux), nops(rs));
  print((ans), (aux), (rs));
  print("mame to T", T);

  if ans = {} then
    map(proc(a) 
          local LC := coeff(a, LVar(a)); ### chyba! to je koeficient u lineárního členu
          `resolve/fails/collect`( `if`(type(a, linear(LVar(a))), 'linear', 'nonlinear'),
                                  'procname', a, LVar(a), VarL(a),  LC, degree(a, LVar(a)), 'solvable'=type(LC, 'nonzero'))
        end,
        map2(op, 1, rs) union aux);
    `resolve/fails/print`();
    return FAIL;
  else 
    return op(ans);
  fi;
end:

`resolve/lin/reduce` := proc(as, vl)
    local lb, rt, bs;
    lb := `RESOLVE:`; rt := `report/tab`[resolve];      
    bs := map(divideout, as); # remove nonzero factors
    bs := map(Simpl, bs, vl); # Simplify
    bs := remove(proc(a) evalb(a = 0) end, bs);  # remove zero eqs.
    if rt > 4 then report(lb,`reducing `, nops(bs)) fi;    
    bs := map(reduceprod, bs);  # reduce products
    return bs;
end:

