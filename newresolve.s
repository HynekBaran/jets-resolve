#
#  R e s o l v e - the new implementation (not well tested yet)
#

printf("\nUsing the new implementation of resolve (not well tested yet!)\n");

#`resolve/nonresrat` := 3;

#`resolve/nonresrat` := 3;

`resolve/1` := proc()
  local as,bs,as1, as2, cs,  ds, vl,i,ans, A, AL, AN, A1, A0, A1S, A1H, B, ff;
  global `resolve/nonresrat`;
  Report(1, cat(`input `, nops([args])));   
  as := MaP(numer,{args}) minus {0};
  Report(1, cat(`numer `, nops(as))); 
  as := MaP(divideout, as)  minus {0}; # remove nonzero factors
  Report(1, cat(`divideout `, nops(as))); 
  bs := select(type, as, nonzero);
  Report(3, [cat(`contradictory `, nops(bs), ` eqns `), bs]); 
  if bs <> {} then print(op(map(proc(b) b = 0 end, bs)));
    ERROR(`there are contradictory equations`)
  fi;
  
  #as := MaP(Simpl,as);
  #if rt > 1 then report(lb,cat(`Simpl `, nops(as))) fi; 
  as := MaP(reduceprod,as) minus {0};  
  Report(1, cat(`reduceprod `, nops(as))); 
  
  A := MaP(`resolve/collectdata`, convert(as,list), source=''procname'');
  A := sizesort(A, a->a:-price);
  AL, AN := selectremove(a->a:-kind = 'linear', A); # nonlin, lin
  A1, A0 := selectremove(a->a:-solvable=true, AL); # resolvable, nonresolvable
  A1S, A1H := selectremove( a -> (nops(a:-Vars)<=1) # simple, hard 
                            # or a:-rest=0 or type(a:-subs, monomial(constant, a:-Vars))
                            #a->a:-price<2 
                            #or type(a:-LC, numeric) or a:-leadLinCoeffVars={} 
                            , A1);                       

  Reportf(1, ["There are %a linear resolvable (%a simple and %a hard),"
                    " %a linear NONresolvable and %a NONlinear eqs. Prices and sizes are:\n"
                    "LIN. RESolv.: %a,\nLIN. NONresolv: %a;\nNONLIN: %a.\n", 
                    nops(A1), nops(A1S), nops(A1H), nops(A0), nops(AN), 
                    map(a->[a:-price,a:-size], A1), 
                    map(a->[a:-price,a:-size], A0), 
                    map(a->[a:-price,a:-size], AN)]); 
  Report(2, `if`(nops(A1)>0,  
                 sprintf("Linear resolvable eqs properties are [price, size, VarL, LC]:\n%s",
                          StringTools:-Join(map(a -> sprintf("%q\n",[a:-price,a:-size,a:-Vars, a:-LC]), A1))),
                 "No linear resolvable equation found.")) ; 
  Report(3,  [cat("Linear NONresolvable eqs properties are [price, size, VarL, LC]:\n%s",
                                "NONlinear eqs properties are [price, size, Vars]:\n%s"), 
              StringTools:-Join(map(a -> sprintf("%q\n",[a:-price, a:-size, a:-Vars, a:-LC]), A0)),
              StringTools:-Join(map(a -> sprintf("%q\n",[a:-price, a:-size, a:-Vars]), AN))]) ; 
  Report(4,  `if`(nops(A1)>0, 
                   sprintf("LIN RESolvable eqs [price, size, eq, leadVar]:\n%s"
                           "LIN NONresolvable eqs [price, size, eq, leadVar]:\n%s",
                           StringTools:-Join(map(a -> sprintf("%q\n",[a:-price,a:-size,a:-expr,a:-Vars[1]]), A1)),
                           StringTools:-Join(map(a -> sprintf("%q\n",[a:-price,a:-size,a:-expr,a:-Vars[1]]), A0))),
                   ""));                             
  
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
    `resolve/reportfail`(AL,AN);  
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
  
  vl := ListTools:-Reverse(sort([op(`union`(op(map(a -> convert(a:-Vars,set), B))))],  `Vars/<<`)); # present Vars in resolvable eqs.
  if vl = [] then ERROR(`no unknowns`, as) fi;  
  ##cs := map(a -> a:-expr, B);
  #DoReports(resolve, cs, comment=cat(" resolve selection:\n", 
  #     sprintf("# prices=%q\n", map(a->a:-price, B)),
  #     sprintf("# sizes =%q\n", map(size, B)),
  #     sprintf("# LVars=%q\n", map(a->a:-Vars[1], B))));  
  
  ans := `resolve/lin`(convert(B, set), vl, ForceFail=ff);
  
  DoReports(resolve, [ans],comment=" resolve output");
  return (ans);
  #####fi;
end:

`resolve/collectdata` := proc(b, {source:=NULL}) 
  local a, V, LC, LCV, LM, r,s, Cs, Ms, deg;
  local lb := `RESOLVE:`, rt := `report/tab`[resolve];
  a := Simpl(b);  
  V := VarL(b);
  if nops(V)=0 then # no unknowns
    tprint("No unknowns in ", a);
    return NULL;
  fi;

  #a := `resolve/lin/reduce`(a, V);
  #if not(frontend(ispoly, [a, linear, V[1], 'r', 'LC'])) then  # nonlinear or non-polynomial case  
  

  #Cs, Ms, deg := coeffsV(a, V);    
  #LC := Cs[1]; LM := Ms[1]; ### bug, leading monimial can be at arbitrary position in the list          
  LC, LM, deg := coeffL(a,V);  

  
  if not(type(a, linear(V[1]))) then  
    # nonlinear or non-polynomial case
    if rt > 5 then printf("Nonlinear case, expr=%a, VarL=%a, LC=%a\n",a,V,LC); fi;
    assert([not(type(a, linear(V[1]))), 
          "Implementation error, failed to compute leading coeff (in VarL %a) of linear expression %a", 
          V,a], callstackskip=1);
    return compat[Record[packed]](
                          "expr"=a, 
                          "reduced"=NULL,                          
                          "kind"='nonlinear',
                          "Vars"=V, 
                          "degree"=deg,
                          "LC"=LC,
                          "LM"=LM,                          
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
    assert([type(a, linear(V[1])), 
            "Implementation error, found leading coeff %a (in VarL %a) of nonlinear expression %a", 
            Cs[1], V, a], callstackskip=1);
   
    LC := collect(LC, V, simpl, distributed); 
    r := collect(a-LC*LM, V, simpl, distributed);
    #s := collect(-r/LC, V, simpl, distributed);
    #LCV := Vars(LC);
    Report(3, ["LC"=LC, "LM"=LM, "deg"=deg, "V"=V, "r"=r, Cs, Ms]);
    return compat[Record[packed]](
                          "expr"=a, 
                          "reduced"=NULL,
                          "kind"='linear',
                          "Vars"=V, 
                          "degree"=deg,
                          "LC"=LC,                          
                          "LM"=LM,                          
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

coeffsV := proc(F, vs := Vars(F), {CF::{procedure,name}:=proc(x) option inline; x end})
  description "collects a given polynomial w. r. to its variables "
              "and returns list of coefficients, list of monomials and degree w. r. to leading variable."
               "keyword CF may specify a collecting function (applied to coefficients)";
  local f, k, l, d ;
  f := collect(F, vs, CF, distributed);
  k := coeffs(f, vs[1], l); 
  d := max(op(map(degree, [l], vs[1])));
  [k],[l], d;
end:


coeffL := proc(F, vs := Vars(F), {CF::{procedure,name}:=proc(x) option inline; x end})
  description "collects a given polynomial w. r. to its variables "
              "and returns leading coefficient, leading monomial and degree w. r. to leading variable."
               "keyword CF may specify a collecting function (applied to coefficients)";
  local f, LC, LM, d ;
  f := collect(F, vs, CF, distributed);
  LC := lcoeff(f, vs[1], LM); 
  d := degree(LM, vs[1]);
  LC, LM, d;
end:

### linear resolve

`resolve/lin` := proc(ds,vl,{ForceFail::truefalse:=false})
  global maxsize, RESOLVE, `resolve/result/suppressedminsize` := NULL;
  local bs,v,cs,ls,ns,ps,p,q,qs,ans,aux,rs,rt,lb, rat, os, os1;
  lb := `RESOLVE:`; rt := `report/tab`[resolve];
  if ForceFail=true then tprint("Enforced linear failure.") fi;

  if rt > 1 then report(lb,cat(`resolving `, nops(ds),` eq.`)) fi; 
  ans := {}; rs := {}; os := {};

  bs := map(proc(d) d:-reduced := `resolve/lin/reduce`(d:-expr, vl); return d; end, ds); # add reductions to ds data records 
  bs := remove(proc(d) evalb(d:-reduced = 0) end, bs);  # remove zero eqs.
 
  if rt > 0 then report(lb,`resolving`, nops(ds), `out of`, nops(ds), `eqns in `, nops(vl), `unknowns`) fi; 

  for v in vl do # for v running through all Vars in reverse Varordering
    if rt > 4 then report(lb,`resolving with respect to`, v) fi; 
    #`resolve/lin/reduce`(bs, vl); ### called above
    cs := select(proc(b) has(b:-reduced, v) end, bs);  # cs = subset of bs with v 
    if rt > 2 then report(lb,`resolving`, nops(cs), `equations`, `with respect to`, v, `: `, cs) fi; 
    bs := bs minus cs;  # bs = subset without v
    ### linear?
    ls, ns := selectremove(a->a:-kind='linear', cs);  # ls = subset of cs linear in v
    
    if ForceFail=true then
      # printf("Enforced linear failure (w. r. to %a).\n", v);
      rs := rs union map(proc(a,v) [a,v] end, cs, v)  # move cs to rs   
    else   
      if rt > 4 then report(lb, nops(ls), `of them linear:`, ls) fi; 
      ### solvable?
      ps, os1 := selectremove(a->(a:-solvable=true), ls);
      ###map(proc(a) T[a]['solvable'] :=  evalb(a in ps) end, ls);
      os := os union os1; # save linear but nonresolvable for future
      if rt > 3 then report(lb, `Solving `, nops(cs),  `eqns w. r. to`,  v, nops(ls), 
                                ` of them linear`, nops(ps), ` of them resolvable.`) fi; 
      if ps <> {} then # if solvable eqs,
        qs := map(`resolve/lin/1`, ps, v, vl); # solve all ps
        if rt > 4 then report(lb,`available solutions:`, qs) fi; 
        qs := sizesort([op(qs)], size);
        q := op(1,qs);
        if rt > 4 then report(lb,`using solution:`, q) fi; 
        ###bs := bs union map(`resolve/lin/reduce`, map(`resolve/subs`, cs, v, q), vl);
        if rt > 4 then report(lb,`back substituted system:`, bs) fi; 
        ans := {v = q} union map(proc(a,v,q) 
                                    op(1,a) = `resolve/subs`(op(2,a), v, q) end, 
                                 ans, v, q)
      else 
        # try to subtract pairs of equations; not implemented yet
        rs := rs union map(proc(a,v) [a:-reduced,v] end, cs, v)  # move cs to rs
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
  
  ### rat := `resolve/nonresrat/test`(os, map(lhs-rhs, ans)); 

  Report(0, [`bobo`, nops(ans), nops(aux), nops(rs)]);
  Report(3, ["soso", ans, aux, rs]);


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

`resolve/lin/1` := proc(p,v, vl) Simpl(-coeff(p:-reduced,v,0)/coeff(p:-reduced,v,1), vl) end:

`resolve/lin/reduce` := proc(a, vl)
    local b;
    b := divideout(a); # remove nonzero factors
    b := Simpl(b, vl); # Simplify
    b := reduceprod(b);  # reduce products
    return b;
end:

`resolve/lin/price` := proc(r)  option inline; size(r) end:

`resolve/reportfail` := proc(AL, AN)
  map(`resolve/reportfail/lin`, AL);
  map(`resolve/reportfail/nonlin`, AN);
  tprint(sprintf("Resolve failed (%a linear, %a NONlinear).", nops(AL), nops(AN)));  
  FAIL;
end:

`resolve/reportfail/lin` := proc(a)
  tprint(sprintf("Linear resolving failed in %a:", a:-Vars[1]));
  #print(a:-expr);
  print(a:-LC*a:-Vars[1]="..."); # ... = -a:-rest
end:

`resolve/reportfail/nonlin` := proc(a)
  tprint(sprintf("NONLinear resolving failed in %a:", a:-Vars[1]));
  print(a:-expr);
end:


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

`resolve/fails/table/counter` := NewIntSeq():

`resolve/fails/clear` := proc()
  global `resolve/fails/table`, `resolve/fails/table/counter`;
  `resolve/fails/table` := table();
  `resolve/fails/table/counter`('set'=0);
end:

`resolve/fails/collect` := proc(kind::symbol, source::uneval, expr, LV, Vs::list, LC, deg::integer, {solvable::truefalse:=NULL}, $)
  global RESOLVE, `resolve/fails/table`, `resolve/fails/table/counter`;
  local i ;
  i := `resolve/fails/table/counter`();
  # backward compatibility
  if kind='linear' then
    RESOLVE := [op(RESOLVE), [LC, LV, -(expr-LC*LV)]]
  elif kind='nonlinear' then
    RESOLVE := [op(RESOLVE), [expr, LV]]
  fi;
  # central fail storage
  `resolve/fails/table`[i] := table([
        ':-kind' = kind, 
        ':-source' = 'source', 
        ':-expr' = expr, 
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
    tail := T['expr'] - T['LC']*T['LV'];
    print (smash(T['LC'])*T['LV'] = -smash(tail));    
  elif kind = 'nonlinear' then
    printf("^%a", T['deg']);
    print(smash(T['expr']));
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
  #print(''procname'', inds, `resolve/fails/table`);
  map(`resolve/fails/print/1`, inds);  
end:
