# Orthogonal Arrays and Analysis Formulas

Standard orthogonal arrays for screening and main-effect estimation in materials science and engineering experiments.

## L9 Orthogonal Array (3^4)

4 factors, 3 levels each, 9 runs.

| Run | A | B | C | D |
|-----|---|---|---|---|
| 1 | 1 | 1 | 1 | 1 |
| 2 | 1 | 2 | 2 | 2 |
| 3 | 1 | 3 | 3 | 3 |
| 4 | 2 | 1 | 2 | 3 |
| 5 | 2 | 2 | 3 | 1 |
| 6 | 2 | 3 | 1 | 2 |
| 7 | 3 | 1 | 3 | 2 |
| 8 | 3 | 2 | 1 | 3 |
| 9 | 3 | 3 | 2 | 1 |

## L16 Orthogonal Array (4^5)

5 factors, 4 levels each, 16 runs.

| Run | A | B | C | D | E |
|-----|---|---|---|---|---|
| 1 | 1 | 1 | 1 | 1 | 1 |
| 2 | 1 | 2 | 2 | 2 | 2 |
| 3 | 1 | 3 | 3 | 3 | 3 |
| 4 | 1 | 4 | 4 | 4 | 4 |
| 5 | 2 | 1 | 2 | 3 | 4 |
| 6 | 2 | 2 | 1 | 4 | 3 |
| 7 | 2 | 3 | 4 | 1 | 2 |
| 8 | 2 | 4 | 3 | 2 | 1 |
| 9 | 3 | 1 | 3 | 4 | 2 |
| 10 | 3 | 2 | 4 | 3 | 1 |
| 11 | 3 | 3 | 1 | 2 | 4 |
| 12 | 3 | 4 | 2 | 1 | 3 |
| 13 | 4 | 1 | 4 | 2 | 3 |
| 14 | 4 | 2 | 3 | 1 | 4 |
| 15 | 4 | 3 | 2 | 4 | 1 |
| 16 | 4 | 4 | 1 | 3 | 2 |

## L25 Orthogonal Array (5^6)

6 factors, 5 levels each, 25 runs.

| Run | A | B | C | D | E | F |
|-----|---|---|---|---|---|---|
| 1 | 1 | 1 | 1 | 1 | 1 | 1 |
| 2 | 1 | 2 | 2 | 2 | 2 | 2 |
| 3 | 1 | 3 | 3 | 3 | 3 | 3 |
| 4 | 1 | 4 | 4 | 4 | 4 | 4 |
| 5 | 1 | 5 | 5 | 5 | 5 | 5 |
| 6 | 2 | 1 | 2 | 3 | 4 | 5 |
| 7 | 2 | 2 | 3 | 4 | 5 | 1 |
| 8 | 2 | 3 | 4 | 5 | 1 | 2 |
| 9 | 2 | 4 | 5 | 1 | 2 | 3 |
| 10 | 2 | 5 | 1 | 2 | 3 | 4 |
| 11 | 3 | 1 | 3 | 5 | 2 | 4 |
| 12 | 3 | 2 | 4 | 1 | 3 | 5 |
| 13 | 3 | 3 | 5 | 2 | 4 | 1 |
| 14 | 3 | 4 | 1 | 3 | 5 | 2 |
| 15 | 3 | 5 | 2 | 4 | 1 | 3 |
| 16 | 4 | 1 | 4 | 2 | 5 | 3 |
| 17 | 4 | 2 | 5 | 3 | 1 | 4 |
| 18 | 4 | 3 | 1 | 4 | 2 | 5 |
| 19 | 4 | 4 | 2 | 5 | 3 | 1 |
| 20 | 4 | 5 | 3 | 1 | 4 | 2 |
| 21 | 5 | 1 | 5 | 4 | 3 | 2 |
| 22 | 5 | 2 | 1 | 5 | 4 | 3 |
| 23 | 5 | 3 | 2 | 1 | 5 | 4 |
| 24 | 5 | 4 | 3 | 2 | 1 | 5 |
| 25 | 5 | 5 | 4 | 3 | 2 | 1 |

## Range Analysis (极差分析)

For each factor, compute the following after completing all runs:

### Step 1: Sum by level (K_i)

For factor A at level j:

$$K_{A,j} = \sum_{k \in \text{runs where } A = j} y_k$$

where $y_k$ is the response value for run $k$.

### Step 2: Mean by level (k_i)

$$k_{A,j} = \frac{K_{A,j}}{n_j}$$

where $n_j$ is the number of runs at level $j$.

### Step 3: Range (R)

$$R_A = \max(k_{A,j}) - \min(k_{A,j})$$

The factor with the largest R is the most influential factor.

### Optimal combination prediction

The optimal level for each factor is the level with the best $k_i$ value (highest for "larger-is-better", lowest for "smaller-is-better", closest to target for "nominal-is-best").

Predicted optimal response:

$$\hat{y}_{opt} = \bar{y} + \sum_{i} (k_{i,opt} - \bar{y})$$

where $\bar{y}$ is the grand mean of all runs.

## ANOVA Table

For a single-factor or multi-factor classical design:

| Source | SS | df | MS | F |
|--------|-----|-----|-----|-----|
| Factor A | $SS_A$ | $a - 1$ | $MS_A = SS_A / (a-1)$ | $F_A = MS_A / MS_E$ |
| Factor B | $SS_B$ | $b - 1$ | $MS_B = SS_B / (b-1)$ | $F_B = MS_B / MS_E$ |
| Error | $SS_E$ | $N - a - b + 1$ | $MS_E = SS_E / (N-a-b+1)$ | — |
| Total | $SS_T$ | $N - 1$ | — | — |

Where:

- $a$ = number of levels of factor A
- $b$ = number of levels of factor B
- $N$ = total number of runs

### Sum of squares formulas

$$SS_T = \sum_{i=1}^{N} y_i^2 - \frac{(\sum y_i)^2}{N}$$

$$SS_A = \frac{1}{n_a} \sum_{j=1}^{a} K_{A,j}^2 - \frac{(\sum y_i)^2}{N}$$

$$SS_E = SS_T - SS_A - SS_B$$

### Significance test

Compare $F_A$ to the critical value $F_{\alpha}(a-1, N-a-b+1)$ from the F-distribution table at significance level $\alpha$ (typically 0.05).

If $F_A > F_{crit}$, the factor has a statistically significant effect on the response.
