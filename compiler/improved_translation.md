# Improved translation rules CL3 -> CPS
## Tail translation [e]T c

### Literals and Names 

```
[a]T c

becomes

app c v
````

### Let 

```
[(let () e)]T c => [e]T c


[(let ((n1 e1) (n2 e2)...) e) ]T c

becomes

[e1]N (\v1 (letP (( n1 (id v1)))

        [(let ((n2 e2) ...) e)]T c


       ))
```

### Letrec

```
[(letrec ((f1 (fun (n11 n12...) e1))...) e)] c 

becomes

(letF ((f1 (fun (c_fresh n11 n12 ...)
                [e1]T c_fresh)...))
        [e]T c)

```

### App

```
[(e e1 e2 ...)]T c 

becomes

[e]N(\v[e1]N(\v1[e2]N(\v2...)))
        (appF v c v1 v2 ...))))

```

### If 

```
[(if (@p e1 ...) e2 e3)]T c

becomes

(letC  ((ct (cnt () [e2]T c)))
  (letC ((cf (cnt () [e3]T c)))
        [e1]C ct cf)
)
```

### Logical primitive
```
[(@p e1 e2 ...)]T c 

becomes 

[(if (@p e1 e2 ...) #t #f )]T c

```


### Non logical primitive
```
[(@ p e1 e2)]T c

becomes 

[e1]N(\v1[e2]N(\v2...
        (letP (( n (p v1 v2 ...)))
        AppC c n
        )

```

### Halt 

```
[(halt e)]T c

becomes 

[e]t\v(halt (v))
```

## Conditional translation [e]C ct cf

### Boolean Literal 
```
[a]C ct cf

becomes 

AppC ct a | if a = #t
AppC cf a | if a = #f

```

### Name 

```
[a]C ct cf 

becomes 

[(@p= a #f)]C cf ct  (why reversing ct cf?)
```


### Let

```
[(let () e)]C ct cf 

becomes 

[e]C ct cf


[(let ((n1 e1) (n2 e2) ...) e)] ct cf

becomes 

[e1]N(\v1 (letP((n1 (id v1))))
        [(let ((n2 e2)...) e)]C ct cf
```


### If

```
====================================

[(if e1 #f #t)]C ct cf

becomes

[e1]C cf ct

====================================

[(if e1 #t #f)]C ct cf

becomes 

[(if e1 #f #t)]C cf ct

===================================

[(if e1 e2 #f)]C ct cf

becomes

(letC ((ac (cnt () ([e2]C ct cf)))
        [e1]C ac cf))

====================================

[(if e1 #f e3)]C ct cf

becomes 

[(if e1 e3 #f)]C cf ct

====================================

[(if e1 e2 #t)]C ct cf

becomes

(letC ((ac (cnt () ([e2]C ct cf)))
        [e1]C ac ct))

====================================

[(if e1 #t e3)]C ct cf

becomes 

[(if e1 e2 #t)]C cf ct



====================================

[(if e1 e2 e3)]C ct cf

becomes 

[(if e1 e2 e3 )]N{\v if (@p v #t) ct cf}
```

### Halt

```
[halt e]C ct cf

becomes 

[e]N{\v halt e}
```






