module Random = struct
  let int _ = read_int ()
end

let _ =

  let check1 f =
    let x = f () in
    if x <= 0 then 1
    else 0
  in
  let pred (fx:unit->int):unit->int =
    let x = fx () in
    (fun u -> x - 1)
  in
  let add (f1:unit->int) (f2:unit->int):unit->int =
    let x1 = f1 () in
    let x2 = f2 () in
    (fun u -> x1 + x2)
  in
  let rec sum fx =
    let b = check1 fx in
    if b =  1 then (fun u -> 0)
    else
      let fm = sum (pred fx) in
      add fm fx
  in
  let rec xx (flag:int) fx =
    if flag = 1 then
      sum fx
    else
      xx 1 fx
  in
  let m x = xx 0 (fun u -> x) in
  m (Random.int 0)
