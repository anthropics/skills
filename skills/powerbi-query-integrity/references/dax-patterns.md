# DAX patterns for integrity-checked queries

Replace `Fact`, `Dim`, column and measure names with the model's own.

## 1. Grouped result + census

```dax
-- Query 1: census
DEFINE
    VAR _t =
        SUMMARIZECOLUMNS (
            Dim[Group],
            TREATAS ( { 2026 }, Calendar[Year] ),
            "v", [Sales]
        )
EVALUATE
ROW (
    "n",         COUNTROWS ( _t ),
    "sum_rows",  SUMX ( _t, [v] ),
    "total",     CALCULATE ( [Sales], Calendar[Year] = 2026 ),
    "last_data", MAX ( Fact[Date] )
)

-- Query 2: data
EVALUATE
SUMMARIZECOLUMNS (
    Dim[Group],
    TREATAS ( { 2026 }, Calendar[Year] ),
    "v", ROUND ( [Sales], 0 )
)
ORDER BY [v] DESC
```

If `sum_rows` < `total`, part of the fact table does not reach any `Dim[Group]` value: report the gap as a blank group.

## 2. Top N + "Rest" row that closes to the total

```dax
DEFINE
    VAR _all =
        ADDCOLUMNS ( VALUES ( Dim[Customer] ), "v", [Sales] )
    VAR _top = TOPN ( 20, _all, [v], DESC )
    VAR _rest =
        ROW ( "Customer", "Rest", "v", SUMX ( _all, [v] ) - SUMX ( _top, [v] ) )
EVALUATE
UNION ( _top, _rest )
ORDER BY [v] DESC
```

Census: `n` = 21 rows expected; the sum of `v` must equal `[Sales]`.

## 3. Snapshot table: filter to the latest date

```dax
DEFINE
    VAR _last = CALCULATE ( MAX ( Balance[Date] ), ALL ( Balance ) )
EVALUATE
SUMMARIZECOLUMNS (
    Dim[Branch],
    TREATAS ( { _last }, Balance[Date] ),
    "balance", ROUND ( [Balance Amount], 0 )
)
ORDER BY [balance] DESC
```

Detecting a snapshot table: `COUNTROWS ( Balance ) / DISTINCTCOUNT ( Balance[Date] )` is large and roughly constant.

## 4. Freshness and cross-model check (one row per model)

```dax
EVALUATE
ROW (
    "rows",      COUNTROWS ( Fact ),
    "control",   [Sales],
    "last_data", MAX ( Fact[Date] )
)
```

Run it on each model that loads the same source; matching values mean both were refreshed together.

## 5. Pagination by key range (last resort)

```dax
EVALUATE
CALCULATETABLE (
    SUMMARIZECOLUMNS ( Fact[Key], "v", [Sales] ),
    Fact[Key] >= 1, Fact[Key] < 50001
)
ORDER BY Fact[Key]
```

Pair each page with its own census over the same range, and check that the page totals add up to the overall total.
