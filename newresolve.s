#
#  R e s o l v e - the new implementation (not well tested yet)
#

printf("\nUsing the new implementation of resolve (not well tested yet!)\n");

#`resolve/nonresrat` := 3;

#`resolve/nonresrat` := 3;

`resolve/1` := proc()
  local as,bs,as1, as2, cs,  ds, vl,i,ans, A, AL, AN, A1, A0, A1S, A1H, AE, APD, B, ff;
  global `resolve/nonresrat`;
  Report(2, cat(`input `, nops([args])));   
  as := MaP(numer,{args}) minus {0};
  Report(2, cat(`numer `, nops(as))); 
  as := MaP(divideout, as)  minus {0}; # remove nonzero factors
  Report(2, cat(`divideout `, nops(as))); 
  bs := select(type, as, nonzero);
  Report(3, [cat(`contradictory `, nops(bs), ` eqns `), bs]); 
  if bs <> {} then print(op(map(proc(b) b = 0 end, bs)));
    ERROR(`there are contradictory equations`)
  fi;
  
  #as := MaP(Simpl,as);
  #if rt > 1 then report(lb,cat(`Simpl `, nops(as))) fi; 
  as := MaP(reduceprod,as) minus {0};  
  Report(2, cat(`reduceprod `, nops(as))); 
  
  A := MaP(`resolve/data/collect`, convert(as,list), source=''procname'');
  A := sizesort(A, a->a:-price);
  AL, AN := selectremove(a->a:-kind <> 'nonlinear', A); # nonlin, lin
  A1, A0 := selectremove(a->a:-solvable=true, AL); # resolvable, nonresolvable
  A1S, A1H :=`resolve/simplehard`(A1);                       

  Reportf(1, ["There are %a linear resolvable (%a simple and %a hard),"
                    " %a linear NONresolvable and %a NONlinear eqs. Prices, sizes, and leading monomials are:\n"
                    "LIN. RESolv.: %a,\nLIN. NONresolv: %a;\nNONLIN: %a.\n", 
                    nops(A1), nops(A1S), nops(A1H), nops(A0), nops(AN), 
                    map(a->[a:-price,a:-size, a:-LM], A1), 
                    map(a->[a:-price,a:-size, a:-LM], A0), 
                    map(a->[a:-price,a:-size, a:-LM], AN)]); 

  if nops(A1) > 0 then 
    Reportf(2, ["Linear resolvable eqs properties are [price, size, VarL, LC]:\n%s",
                StringTools:-Join(map(a -> sprintf("%q\n",[a:-price,a:-size,a:-Vars, a:-LC]), A1))]) ; 
  fi;
  if nops(A0) > 0 then 
    Reportf(2,  ["Linear NONresolvable eqs properties are [price, size, VarL, LC]:\n%s", 
                StringTools:-Join(map(a -> sprintf("%q\n",[a:-price, a:-size, a:-Vars, a:-LC]), A0))]) ; 
  fi;
  if nops(AN) > 0 then 
    Reportf(2,  ["NONlinear eqs properties are [price, size, VarL, deg, LM, LC]:\n%s", 
                 StringTools:-Join(map(a -> sprintf("%q\n",[a:-price, a:-size, a:-Vars, a:-degree, a:-LM, a:-LC]), AN))]) ; 
  fi;
  Reportf(4, `if`(nops(A1)>0,
                  ["Linear resolvable eqs [price, size, leadVar, eq]:\n%s",
                      StringTools:-Join(map(a -> sprintf("%q\n",[a:-price,a:-size,a:-LM,a:-expr]), A1))],
                   "No linear resolvable equation found."));

  Reportf(4, `if`(nops(A0)>0,
                  ["LIN NONresolvable eqs [price, size, leadVar, eq]:\n%s",
                      StringTools:-Join(map(a -> sprintf("%q\n",[a:-price,a:-size,a:-LM,a:-expr]), A0))],
              "No linear NONresolvable eqs found."));
                          
  Reportf(4, `if`(nops(AN)>0,
                  ["Nonlinear eqs [price, size, leadMono, eq]:\n%s",
                      StringTools:-Join(map(a -> sprintf("%q\n",[a:-price,a:-size,a:-LM,a:-expr]), AN))],
                  "No NONlinear eqs found."));
    
  
#DoReports(resolve,  [op(map(a->a:-expr,A1)), op(map(a->a:-expr,A0)),  op(map(a->a:-expr,AN))], 
#     comment=cat(sprintf(" resolve input (#lin resolvable: %a (%a of them simple), #lin non-res.: %a #nonlin: %a):\n", 
#				nops(A1), nops(A1S), nops(A0), nops(AN)), 
#       sprintf("# prices(res-lin)=%q\n", map(a->a:-price, A1)),
#       sprintf("# sizes(res-lin) =%q\n", map(a->a:-size, A1)),
#       sprintf("# LVars(res-lin)=%q\n", map(a->a:-Vars[1], A1)),
#       
#       sprintf("# prices(nonres-lin)=%q\n", map(a->a:-price, A0)),
#       sprintf("# sizes(nonres-lin) =%q\n", map(a->a:-size, A0)),
#       sprintf("# LVars(nonres-lin)=%q\n", map(a->a:-Vars[1], A0)),
#       
#       sprintf("# prices(nonlin)=%q\n", map(a->a:-price, AN)),
#       sprintf("# sizes(nonlin) =%q\n", map(a->a:-size, AN)),
#       sprintf("# LVars(nonlin)=%q\n", map(a->a:-Vars[1], AN))));
    
  if nops(A1) = 0 then
    ######################`resolve/reportfail`(AL,AN);  
     B := A;
  #####                                                  
  else 
    B := A1S; # all simple
    if nops(B)=0 and nops(A1H)>0 then B:= [op(B), A1H[1]] fi; # no simple, take 1 hard (if exists) 
    #if nops(A1H)>0 then B:= [op(B), A1H[1]] fi; # all simple and 1 hard (if exists)  
  fi; ####
  #map(lprint@lprint, AL);lprint(); map(lprint@lprint, AN);
  

  if assigned(`resolve/nonresrat`) and nops(A1)>0 and nops(A0)>0 
    and A1[1]:-price>A0[1]:-price*`resolve/nonresrat` then
    ff := true;     
    B := [A0[1]];
    #B := AL;  
    printf("Forcing linear failure:\n"
       "Resolvable expression of price %a and size %a"
       " overlapped nonresolvable expression price %a and size %a (`resolve/nonresrat`=%a).\n",
     A1[1]:-price,  A1[1]:-size, A0[1]:-price,  A0[1]:-size,  `resolve/nonresrat` );
    #printf("All %a expressions (including %a resolvable) are considered as nonresolvable.\n", nops(B), nops(A1));
    printf("Of all %a expressions (including %a resolvable), first one choosen to be resolved.\n", nops(B), nops(A1));
  else
    ff := false;
  fi;
  
  vl :=`resolve/data/get/Vars`(B); # present Vars in resolvable eqs.
  if vl = [] then ERROR(`no unknowns`, as) fi;  
  ##cs := map(a -> a:-expr, B);
  #DoReports(resolve, cs, comment=cat(" resolve selection:\n", 
  #     sprintf("# prices=%q\n", map(a->a:-price, B)),
  #     sprintf("# sizes =%q\n", map(size, B)),
  #     sprintf("# LVars=%q\n", map(a->a:-Vars[1], B))));  
   
  ans := `resolve/lin`(convert(B, set), vl, ForceFail=ff);

  # if no usable results, lets try to generate pseudoremainders of polynomial pairs
  if ans = FAIL and nops(AN)>=2 then

    Reportf(2, ["No solvable linear eqs found, trying to combine nonlinear eqs pairs into linear"]);
    AE := `resolve/nonlin/combine`(AN);
    Reportf(1, ["Combining %a nonlinear eqs given %a linear results", nops(AN), nops(AE)]);
    Reportf(2, ["...witch properties are [price, size, VarL, LC]:\n%s",
                StringTools:-Join(map(a -> sprintf("%q\n",[a:-price,a:-size,a:-Vars, a:-LC]), AE))]); 
    Reportf(0, ["Lets resolve combined %a linear eqs (out of %a nonlinear)...", nops(AE), nops(AN)]); 
    ans := `resolve/lin`(convert(AE, set), ForceFail=ff, keepfails);
  fi;    
  
  #  if still no usable results, lets try to linearize nonlinear eqs by pd (linderive)
  if ans = FAIL and nops(AN)>0 then
    Reportf(2, ["No solvable linear eqs found, trying to linearize eqs by linderive"]);
    # APD := convert(`resolve/nonlin/pd`(convert(AN,set)), list);
    APD := convert(linderive(op(AN)), list);
    Reportf(1, ["Deriving %a nonlinear eqs given %a linear results", nops(AN), nops(APD)]);
    Reportf(2, ["...witch properties are [price, size, VarL, LC]:\n%s",
                StringTools:-Join(map(a -> sprintf("%q\n",[a:-price,a:-size,a:-Vars, a:-LC]), APD))]); 
    Reportf(0, ["Derived %a linear eqs from %a nonlinear", nops(APD), nops(AN)]); 
    ans := `resolve/lin`(convert(APD, set), ForceFail=ff, keepfails);
  fi;
  
  DoReports(resolve, [ans],comment=" resolve output");
  if ans = FAIL then `resolve/fails/print`(); fi;
  return (ans);
  #####fi;
end:


`resolve/simplehard` := proc(as::list(record))
  selectremove( a -> (nops(a:-Vars)<=1 or a:-rest=0 ) # simple, hard 
                            # or type(a:-subs, monomial(constant, a:-Vars))
                            #a->a:-price<2 
                            #or type(a:-LC, numeric) or a:-leadLinCoeffVars={} 
                            , as);
end: 

### `resolve/data` toolbox
# instead of algrebraic expressions, records are used to avoid multiple computations on the same expression
# the original expression is stored in r:-'expr' slot

`resolve/data/collect` := proc(b::algebraic, {source:='`?`'}, $)
  local a, Vs, LC, LCV, LM, r,s, Cs, Ms, deg;
  a := Simpl(b);  
  Vs := VarL(b);
  if nops(Vs)=0 then # no unknowns
    Reportf(0, ["No unknowns in %a", a]);
    return compat[Record[packed]](
                          "expr"=a, 
                          "reduced"=NULL,                          
                          "kind"='unknownless',
                          "Vars"=Vs, 
                          "degree"=0,
                          "LC"=a,
                          "LM"=1,  
                          #"LV"=LV,                        
                          "price"=0, 
                          "size"=size(a),
                          "source"=source,
                          "solvable"=FAIL
                          )  
  fi;

  #a := `resolve/lin/reduce`(a, Vs);
  #if not(frontend(ispoly, [a, linear, Vs[1], 'r', 'LC'])) then  # nonlinear or non-polynomial case  
  #Cs, Ms, deg := coeffsV(a, Vs);    
  #LC := Cs[1]; LM := Ms[1]; ### bug, leading monimial can be at arbitrary position in the list          

  LC, LM, deg := coeffL(a,Vs);  

  if not(type(a, linear(Vs[1]))) then  
    # nonlinear or non-polynomial case
    Report(4, ["NONLinear case", "LC"=LC, "LM"=LM, "deg"=deg, "Vs"=Vs]);
    assert([not(type(a, linear(Vs[1]))), 
          "Implementation error, failed to compute leading coeff (in VarL %a) of linear expression %a", 
          Vs,a], callstackskip=1);
    return compat[Record[packed]](
                          "expr"=a, 
                          "reduced"=NULL,                          
                          "kind"='nonlinear',
                          "Vars"=Vs, 
                          "degree"=deg,
                          "LC"=LC,
                          "LM"=LM,  
                          "LV"=Vs[1],                        
                          "price"=infinity, 
                          "size"=size(a),
                          "source"=source
                          #"coeffs"=[C], "monoms"=[M],
                          #":-leadLinCoeffVars"=FAIL
                          #"rest"=a,
                          #"subs"=FAIL
                          )
  else 
    # linear case
    assert([type(a, linear(Vs[1])), 
            "Implementation error, found leading coeff %a (in VarL %a) of nonlinear expression %a", 
            Cs[1], Vs, a], callstackskip=1);
   
    LC := collect(LC, Vs, simpl, distributed); 
    r := collect(a-LC*LM, Vs, simpl, distributed);
    #s := collect(-r/LC, Vs, simpl, distributed);
    #LCV := Vars(LC);
    Report(4, ["Linear case", "LC"=LC, "LM"=LM, "deg"=deg, "Vs"=Vs]);
    return compat[Record[packed]](
                          "expr"=a, 
                          "reduced"=NULL,
                          "kind"='linear',
                          "Vars"=Vs, 
                          "degree"=deg,
                          "LC"=LC,                          
                          "LM"=LM,  
                          "LV"=Vs[1],                         
                          "price"=`resolve/lin/price`(a), 
                          "size"=size(a),
                          "source"=source,                          
                          #'coeffs'=[C], 'monoms'=[M],
                          #'leadLinCoeffVars'=LCV
                          "solvable"=evalb(type(LC,nonzero)),
                          "rest"=r
                          #'subs'=s 
                          )
  fi
end:

`resolve/data/get/expr` := proc(a) option inline; `if`(type(a, sequential), map(b->b:-expr, a), a:-expr) end:

`resolve/data/get/Vars` := proc(es::sequential(record))
  VarL(`union`(op(map(a -> convert(a:-Vars,set), convert(es, list)))));
end;

coeffsV := proc(F, Vs := Vars(F), {CF::{procedure,name}:=proc(x) option inline; x end})
  description "collects a given polynomial w. r. to its variables "
              "and returns list of coefficients, list of monomials and degree w. r. to leading variable."
               "keyword CF may specify a collecting function (applied to coefficients)";
  local f, k, l, d ;
  f := collect(F, Vs, CF, distributed);
  k := coeffs(f, Vs[1], l); 
  d := max(op(map(degree, [l], Vs[1])));
  [k],[l], d;
end:


coeffL := proc(F, Vs := Vars(F), {CF::{procedure,name}:=proc(x) option inline; x end})
  description "collects a given polynomial w. r. to its variables "
              "and returns leading coefficient, leading monomial and degree w. r. to leading variable."
               "keyword CF may specify a collecting function (applied to coefficients)";
  local f, LC, LM, d ;
  f := collect(F, Vs, CF, distributed);
  LC := lcoeff(f, Vs[1], LM); 
  d := degree(LM, Vs[1]);
  LC, LM, d;
end:


### linearize nonlinear eqs by pd w. r. to its vars

#`resolve/nonlin` := proc(ns, LV)
#  `union`(op(map(`linderive/1`, ns, LV)))
#end:

linderive := proc()
  description "given expression(s) nonlinear in leading Var, derive them in order to obtain linear consequences";
  `union`(op(map(`linderive/1`, [args])))
end:

`linderive/1` := overload([
  proc (r::record, $) option overload(callseq_only);
    map(`resolve/data/collect`@simpl, `linderive/1`(r:-expr, (r:-Vars)[1]))
  end,
  proc (a::algebraic, LV := LVar(a))
    map2(pd, a, vars(LV, forceError=true))
  end
]):



### linearize combined nonlinear pairs (by multiples of remainders)

`resolve/nonlin/combine` := proc(as::list(record))
  local Vs, res;
  # collect leading Vars 
  Vs := convert(map(proc(a)  a:-Vars[1]; end, as), set);
  # apply  `resolve/nonlin/combine/V` on subclasses of as distinguished by leading Var
  res := map(proc(LV) local bs := select(a -> a:-Vars[1] = LV, as); `resolve/nonlin/combine/LV`(LV, bs) end, Vs);
  return sizesort(map(`resolve/data/collect`, res, source='procname'), a->a:-size);
end:

`resolve/nonlin/combine/LV` := proc (LV, bs)
  local cs;
  Reportf(1, ["combining %a nonlinear eqs with leading Var %a", nops(bs), LV]);
  return `resolve/nonlin/combine/LV/r`(bs);
end;

`resolve/nonlin/combine/LV/r` := proc(bs)
  local rfg, rgf, rr;
  if nops(bs) < 2 then 
    return NULL
  else
    rfg := op(map2((f,g) -> `resolve/nonlin/combine/2`(f:-expr, g:-expr) , bs[1], bs[2..-1]));
    rgf := op(map2((f,g) -> `resolve/nonlin/combine/2`(g:-expr, f:-expr) , bs[1], bs[2..-1]));
    rr := thisproc(bs[2..-1]);
    return rfg, rgf, rr;
  fi;
end:

`resolve/nonlin/combine/2` := proc(f,g)
  global `resolve/nonlin/combine/2/tool`;
  local Vsf, Vsg, LV, LCf, LCg, cf, cg, tf, tg, df, dg, res;
  Vsf := VarL(f);
  Vsg := VarL(g);
  Report(5, [f,g]);
  # leading Var
  if  Vsf[1] <>  Vsg[1] then 
    error ("Different leading Vars %1, %2",Vsf[1], Vsg[1]); 
  else
    LV :=  Vsf[1];
  fi;
  # assuming Simpl(a, [V1]) is already done;
  # coeficciens and terms
  try
    cf := coeffs(f, LV, tf);
  catch "invalid arguments to coeffs":
     Report(0, ["f not polynomial?", LV, f]);
     return NULL;
  end try;
  try
    cg := coeffs(g, LV, tg);
  catch "invalid arguments to coeffs":
     Report(0, ["g not polynomial?", LV, g]);
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
      Reportf(2, ["Combining polynomials in %a, %a", tf[1], tg[1]]); 
       res := `resolve/nonlin/combine/2/tool`(f, g, LCf, LCg, df, dg, LV, Vsg);
       #res := collect(res, Vsf, simpl, distributed);
    else
      Reportf(2, ["Combining polynomials in %a, %a", tg[1], tf[1]]); 
       res := `resolve/nonlin/combine/2/tool`(g, f, LCg, LCg, dg, df, LV, Vsf);
       #res := collect(res, Vsg, simpl, distributed);
    fi; 
  #fi;
  return res;
end:

`resolve/nonlin/combine/2/tool` := `resolve/nonlin/combine/2/pseudorem`:

`resolve/nonlin/combine/2/pseudorem` := proc (f, g, LCf, LCg, df::integer, dg::integer, LV, Vs::list, $)
  description "Remainder of (appropriate multiple of f) and (g) to avoid div by 0";
  local K, Kf, Kg;
  #K := LCg^(df-dg+1);
  gcd(LCf,LCg^(df-dg+1), Kf, Kg); #### ??????????????????????????
  Reportf(5, ["Combining (%a) * (%a) and %a", Kg, f, g]);
  frontend(rem, [Kg*f, g, LV])
end:

`resolve/nonlin/combine/2/rem` := proc (f, g, LCf, LCg, df::integer, dg::integer, LV, Vs::list, $)
  local res;
  res := frontend(rem, [f, g, LV]);
  if type(LCg, 'nonzero') then
    return res;
  else
    lprint("`resolve2/rem` failed for ", LV, "nonzero coeff is", LCg);
    `resolve/fails/collect`('remainder', 'procname', res, LV, Vs, LCg, [df, dg]);
    return NULL;
  fi;
end:

### linear resolve

`resolve/lin` := overload([
  
  proc(ds::sequential(algebraic), $) option overload(callseq_only);
    local rs := map(`resolve/data/collect`, ds, source='`resolve/lin`');
    `resolve/lin`(rs, _rest);
  end,
  
  proc(ds::sequential(record), vl::list:=`resolve/data/get/Vars`(ds), {ForceFail::truefalse:=false}) option overload(callseq_only);
    global maxsize, RESOLVE, `resolve/result/suppressedminsize` := NULL;
    local bs,v,cs,ls,ns,ps,p,q,qs,ans,aux,rs,rt,lb, rat, os, os1;
    if ForceFail=true then tprint("Enforced linear failure.") fi;
  
    Report(1, cat(`resolving `, nops(ds),` eq.`)); 
    ans := {}; rs := {}; os := {}; 
  
    bs := remove(proc(d) evalb(d:-expr = 0) end, ds);  # remove zero eqs.

    bs := map(`resolve/lin/reduce`, bs, vl); # add reductions to ds data records 
    bs := remove(proc(d) evalb(d:-reduced = 0) end, bs);  # remove zero eqs.

   
    Report(0, [`resolving`, nops(ds), `out of`, nops(ds), `eqns in `, nops(vl), `unknowns`]) ; 
  
    for v in vl do # for v running through all Vars in reverse Varordering
      #`resolve/lin/reduce`(bs, vl); ### called above
      cs := select(proc(b) has(b:-reduced, v) end, bs);  # cs = subset of bs with v 
      Report(2, [`resolving`, nops(cs), `equations`, `with respect to`, v]); 
      Report(5, [`resolving eqs`, `resolve/data/get/expr`(cs), `w.r. to`, v]); 
      Report(6, [`resolving eqs with data`, cs, `w.r. to`, v]); 
      bs := bs minus cs;  # bs = subset without v
      ### linear?
      ls, ns := selectremove(a->(a:-kind='linear' or a:-kind='unknownless'), cs);  # ls = subset of cs linear in v
      
      if ForceFail=true then
        # printf("Enforced linear failure (w. r. to %a).\n", v);
        rs := rs union map(proc(a,v) [a,v] end, cs, v)  # move cs to rs   
      else   
       Report(4, [ nops(ls), `of them linear:`, `resolve/data/get/expr`(ls)]); 
        ### solvable?
        ps, os1 := selectremove(a->(a:-solvable=true or a:-solvable=FAIL), ls);
        os := os union os1; # save linear but nonresolvable for future
        Report(3, [`Solving `, nops(cs),  `eqns w. r. to`,  v, nops(ls), 
                                  ` of them linear`, nops(ps), ` of them resolvable.`]); 
        if ps <> {} then # if solvable eqs,
          qs := map(`resolve/lin/1`, ps, v, vl); # solve all ps
          Report(4, [`available solutions:`, qs]); 
          qs := sizesort([op(qs)], size);
          q := op(1,qs);
          Reportf(3, ["using solution %a=%a", v, q]); 
          bs := bs union map(`resolve/lin/reduce`, map(`resolve/subs`, cs, v, q), vl);
          Report(4, [`back substituted system:`, `resolve/data/get/expr`(bs)]) ; 
          ans := {v = q} union map(proc(a,v,q) 
                                      op(1,a) = `resolve/subs`(op(2,a), v, q) end, 
                                   ans, v, q)
        else 
          # try to subtract pairs of equations; not implemented yet
          rs := rs union map(proc(a,v) [a:-reduced,v] end, cs, v)  # move cs to rs
        fi;
      fi;
    od;
    Report(0, cat(`solved `, nops(ans), ` eq.`)); 
    Report(1, cat(`rejected `, nops(rs), ` eq.`)); 
    Report(2, [`sizes: solved:`, op(sort(map(size,[op(ans)]))), `rejected:`, op(sort(map(size,[op(rs)]))), `left `, nops(bs), ` eq.`]);    
    
    ans := map(Simpl, map(eval,ans), vl);
    
    rs := map(proc(r,vl) [Simpl(op(1,r), vl), op(2,r)] end, rs, vl);
    rs := select(proc(r) evalb(op(1,r) <> 0) end, rs);
    aux := ans;
    ans := select(proc(a) size(a) < maxsize end, ans);
    aux := aux minus ans;
    
    ### rat := `resolve/nonresrat/test`(os, map(lhs-rhs, ans)); 
  
    Report(0, [`bobo`, nops(ans), nops(aux), nops(rs)]);
  
    if ans = {} then
      map(proc(a) 
            local LC := lcoeff(a, LVar(a)); ### je to ok??????
            `resolve/fails/collect`( `if`(type(a, linear(LVar(a))) or Vars(a)={}, 'linear', 'nonlinear'),
                                    '`resolve/lin`', a, LVar(a), VarL(a),  LC, degree(a, LVar(a)), 'solvable'=type(LC, 'nonzero'))
          end,
          map2(op, 1, rs) union aux);
      ###`resolve/fails/print`();
      return FAIL;
    else 
      return op(ans);
    fi;
  end
]):


`resolve/subs` := overload([
  proc(a::record,v,q) option overload(callseq_only);
    `resolve/data/collect`(Simpl(subs(v = q, a:-expr)))
  end,
  proc(a::algebraic,v,q) option overload(callseq_only);
    Simpl(subs(v = q, a)) # Correction: Simpl added 9.7.2007
  end
  ]):


`resolve/lin/1` := proc(p,v, vl) Simpl(-coeff(p:-reduced,v,0)/coeff(p:-reduced,v,1), vl) end:

`resolve/lin/reduce` := proc(a::record, vl)
    local b, res;
    b := divideout(a:-expr); # remove nonzero factors
    b := Simpl(b, vl); # Simplify
    if b=0 then 
      return NULL
    else
      a:-expr := b;
      a:-reduced := reduceprod(b);  # reduce products
      return a;
    fi;
end:

`resolve/lin/price` := proc(r)  option inline; size(r) end:


### resolve fail Reporter

reporters[resolve]:= []:  # no reporting by default
 
AddReporter[resolve] := proc({mode:=incremental, incProc:=`run/getstep`, 
                              handler::name:=default, handlerOpts:=NULL})
  global reporters;
  local r;
  r := CreateDataReporter(args,_options, 
                          ':-outputProc'=`resolve/reporter`, 
                          addOutArgs=(':-handler'=handler, ':-handlerOpts'=handlerOpts));
  reporters[resolve] := [op(reporters[resolve]), r];
end:

`resolve/reporter`:= proc(as,{handler:=default}) # may be used
  local H, hopts, n := 0;
  #printf("Resolving %a expressions (step %a)...\n",nops(as), `run/getstep`());
  if type(handler, indexed) then 
    H := cat(`resolve/reporter/`,op(0,handler)); hopts := op(handler) 
  else 
    H := cat(`resolve/reporter/`,handler) ; hopts := NULL 
  fi;
  cat(op(map(H, as, proc() n := n+1 end, hopts)));
  #printf("(end of resolving step %a).\n", `run/getstep`());
  end:

`resolve/reporter/default` := proc(a, N, {collectFun:=`reporter/CF/id`})
 # [N,i]=[Var=[length,vars], ...]
 local vs, c, e;
 try
   vs := VarL(a);
   c := collect(a, vs, collectFun, distributed);
   #c := polynomMOSortL(a, CF=collectFun);
   sprintf("[%a,%a,%a]=%q\n", `run/getstep`(), N(), size(a), c);
  catch:
    e := lastexception;
    print(e);
    cat(StringTools[FormatMessage](e[2..-1]), " original expression: ", convert(a,string));
  end try;
end:

`reporter/CF/id` := proc(e) e end:

`reporter/CF/X` := proc(e) X[e] end:

`reporter/CF/L` := proc(e)
  local L := length(e);
  if L <= 5 then e
  else [length(e)] fi;
end:

`reporter/CF/Lv` := proc(e)
  local L := length(e);
  if L <= 5 then e
  else [length(e),vars(e)] fi;
end:


#polynomMOSortL := proc(F)
#  description "Sorts polynomial using monomial order `Vars/<<` "
#              "and returns a (sorted) list of its terms"
#              "keyword CF may specify a collecting function (applied to coefficients)";
#  # polynomials in maple cannot be sorted by user-defined ordering  so list must be returned
#  local K, L, S, R;
#  K, L := coeffsV(_passed,_options);
#  S := table(zip(`=`,L,K));
#  R := sort(L, (a,b)->`Vars/<<`(a,b));
#  map(a->S[a]*a, R);
#end:
#
#polynomMOSortCM := proc(F)
#  description "Sorts polynomial using monomial order `Vars/<<` "
#              "and returns a pair of (sorted) lists: coefficients and monomials"
#              "keyword CF may specify a collecting function (applied to coefficients)";
#  # polynomials in maple cannot be sorted by user-defined ordering  so list must be returned
#  local K, L, S, R;
#  K, L := coeffsV(_passed,_options);
#  S := table(zip(`=`,L,K));
#  R := sort(L, (a,b)->`Vars/<<`(a,b));
#  map(a->S[a], R), R;
#end:


`resolve/fail` :=  proc(r, msg) 
  if type(op(1,r), linear(op(2,r))) then 
    tprint(msg, op(2,r));
    print (smash(factor(coeff(op(r),1)))*op(2,r) = -smash(coeff(op(r),0)));
    [coeff(op(r),1), op(2,r), -coeff(op(r),0)] # [a1,x1,-b1] FAIL prvního druhu
  else 
    tprint(`resolving failed for`, op(2,r), `nonlinear `);
    print (smash(op(1,r)));
    [op(1,r), op(2,r)] # [a,x1] FAIL druhého druhu
  fi
end:

`resolve/nonresrat/test` := proc (l, r)
  global  `resolve/nonresrat`;
  local  L, R, Ls, Rs, Lv, Rv, Ls0, Rs0, lb, rt, aux, rat;
  lb := `RESOLVE:`; rt := `report/tab`[resolve];
  if assigned(`resolve/nonresrat`) and nops(l)>0 and nops(r)>0 then
    # find nice but non-resolvable linear eqs  
    L   := convert(l, list); R   := convert(r, list);
    Ls  := map (size, L);    Rs  := map (size, R);    
    Ls0 := min(op(Ls));      Rs0 := min(op(Rs));
    rat := Rs0/Ls0;    
    if (rat > `resolve/nonresrat`) then
      # some reporting
      if rt>0 then
        L := sizesort(L, size);  
        Reportf(0, ["There are %a nonresolvable and %a resolvable lin. eqs., minimal sizes are %a, resp. %a, ratio is %a",  nops(L), nops(R), Ls0, Rs0, rat]) ;
        if rt>1 then
          Lv := map (LVar, L);    
          Rv := map (LVar, R);              
          Reportf(1, ["\nNonresolvables: %a, \nResolvables: %a", zip(`=`, Lv, Ls), zip(`=`, Rv, Rs)]);     
          Reportf(2, ["Minimal nonresolvable is %a", L[-1]]);
          Reportf(3, ["Minimal resolvable is %a", sizesort(R, size)[-1]]);
        fi;
      fi;       
    fi;    
    return rat/`resolve/nonresrat`; # normalize the ratio, the result > 1 triggers FAIL   
  else
    return 0;
  fi;
end:



### resolve failure table

`resolve/fails/table` := `resolve/fails/clear`(): # global

`resolve/fails/table/counter` := NewIntSeq(): # NewIntSeq must be defined BEFORE this line

`resolve/fails/clear` := proc()
  global `resolve/fails/table`, `resolve/fails/table/counter`;
  `resolve/fails/table` := table();
  `resolve/fails/table/counter`('set'=0);
end:

`resolve/fails/collect` := proc(kind::symbol, source::uneval, expr, LV, Vs::list, LC, deg, {solvable::truefalse:=NULL}, $)
  global RESOLVE, `resolve/fails/table`, `resolve/fails/table/counter`;
  local i ;
  i := `resolve/fails/table/counter`();
  Report(5, ["collecting", i, [args]]);
  # backward compatibility
  if kind='linear'  or kind ='remainder' then
    RESOLVE := [op(RESOLVE), [LC, LV, -(expr-LC*LV)]]
  elif kind='nonlinear' then
    RESOLVE := [op(RESOLVE), [expr, LV]]
  else
    error "unknown kind %1", kind;
  fi;
  # central fail storage
  `resolve/fails/table`[i] := table([
        ':-kind' = kind, 
        ':-source' = 'source', 
        ':-expr' = expr, 
        ':-LV' = LV, 
        ':-LM' = LV^deg, 
        ':-deg' = deg,
        ':-LC' = LC, 
        ':-Vs' = Vs, 
        ':-solvable' = solvable]);
end:

`resolve/fails/print/1` := proc(i)
  global `resolve/fails/table`;
  local T, kind, tail, slv;
  T := `resolve/fails/table`[op(i)];
  kind := T[':-kind'];
  tprint(sprintf("%a. %a solving by %a failed in %a", 
                  op(i), kind, T['source'], T['LV']),
         newline=false);
  if kind = 'linear' or kind ='remainder' then
    if T['solvable']=true then printf(" (solvable) ") fi;
    tail := T['expr'] - T['LC']*T['LV'];
    print (smash(T['LC'])*T['LV'] = -smash(tail));    
  elif kind = 'nonlinear' then
    printf("^%a", T['deg']);
    print(smash(T['expr']));
  else
    error "Wrong kind %1", kind;
  fi;
end:


`resolve/fails/print` := proc()
  global `resolve/fails/table`;
  local inds := [indices(`resolve/fails/table`)];
  #print(''procname'', inds, `resolve/fails/table`);
  map(`resolve/fails/print/1`, inds);  
end:
