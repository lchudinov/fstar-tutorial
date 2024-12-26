console.clear();

type st<A> = (x: number) => [a: A, x: number];

const read_and_increment_v0: st<number> = s0 => [s0, s0 + 1];

const inc_twice_v0: st<number> = s0 => {
  const [x, s1] = read_and_increment_v0(s0);
  const [_, s2] = read_and_increment_v0(s1);
  return [x, s2];
}

console.log('read_and_increment_v0(5)', read_and_increment_v0(5));
console.log('inc_twice_v0(5)', inc_twice_v0(5));

const read: st<number> = s => [s, s];
console.log('read(5)', read(5));

const write: st<void> = (s1: number) => [undefined, s1];

console.log('write(5)', write(5));

const bind: <A, B>(f: st<A>, g: (a: A) => st<B>) => st<B> = (f, g) => s0 => {
  const [x, s1] = f(s0);
  return g(x)(s1);
}

const ret: <A>(x: A) => st<A> = x => s => [x, s];

const read_and_increment_v1: st<number> =
  bind(
    read,
    x => bind<void, number>(_ => write(x + 1), _ => ret(x))
  );

console.log(`read_and_increment_v1(5)`, read_and_increment_v1(5));

const read_and_increment_twice: st<number> =
  bind(
    x => read_and_increment_v1(x),
    x => bind<number, number>(x1 => read_and_increment_v1(x1), _ => ret(x))
  );

console.log(`read_and_increment_twice(5)`, read_and_increment_twice(5));
