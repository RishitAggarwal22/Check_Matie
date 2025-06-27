import sys;

def dp(v, l, r, prefix_sum):
    if l == r:
        return v[l]
    elif l == 0:
        return max(
            v[l] + prefix_sum[r] - prefix_sum[l] - dp(v, l+1, r, prefix_sum),
            v[r] + prefix_sum[r-1] - dp(v, l, r-1, prefix_sum)
        )
    else:
        return max(
            v[l] + prefix_sum[r] - prefix_sum[l] - dp(v, l+1, r, prefix_sum),
            v[r] + prefix_sum[r-1] - prefix_sum[l-1] - dp(v, l, r-1, prefix_sum)
        )

def main():
    filename = sys.argv[1]
    with open(filename, 'r') as f:
        lines = f.readlines()
    n = int(lines[0].strip())
    v = list(map(int, lines[1].strip().split()))
    prefix_sum = [0] * n
    prefix_sum[0] = v[0]
    for i in range(1, n):
        prefix_sum[i] = v[i] + prefix_sum[i-1]
    print(dp(v, 0, n-1, prefix_sum))

if __name__ == "__main__":
    main()