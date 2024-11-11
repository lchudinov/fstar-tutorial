function quicksort(l: number[]): number[] {
  if (l.length === 0) {
    return [];
  }
  const [pivot, ...tl] = l;
  const [lo, hi] = partition(pivot, tl);
  return [...quicksort(lo), pivot, ...quicksort(hi)];
}

function partition(pivot: number, l: number[]): [number[], number[]] {
  if (l.length === 0) {
    return [[], []];
  }
  const [hd, ...tl] = l;
  let [lo, hi] = partition(pivot, tl);
  if (hd <= pivot) {
    return [[hd, ...lo], hi];
  } else {
    return [lo, [hd, ...hi]];
  }
}

const arr = [1, 3, 5, 7, 9, 2, 4, 6, 8];

const sortedArr = quicksort(arr);

function sorted(l: number[]): boolean {
  if (l.length === 0 || l.length === 1) {
    return true;
  }
  const [x, y, ...tl] = l;
  return x <= y && sorted([y, ...tl]);
}

console.log(`sortedArr`, sortedArr);
console.log(`sorted ?`, sorted(sortedArr));