"""Workbooks as openpyxl writes them: formulas verbatim, no cached values."""
import sys
from pathlib import Path

from openpyxl import Workbook
from openpyxl.chart import BarChart, Reference

out = Path(sys.argv[1])
out.mkdir(parents=True, exist_ok=True)


def save(name, build):
    wb = Workbook()
    ws = wb.active
    ws.title = "S"
    build(ws)
    wb.save(out / f"{name}.xlsx")


def noprefix(ws):
    ws["A1"], ws["A2"], ws["B1"], ws["B2"] = 1, 2, 10, 20
    ws["C1"] = "=XLOOKUP(2,A1:A2,B1:B2)"


def cycle(ws):
    ws["A1"], ws["B1"], ws["C1"] = "=B1+1", "=A1+1", "=A1*10"


def badformat(ws):
    ws["A1"] = 5
    ws["A1"].number_format = "0 kg"
    ws["A2"] = "=A1*2"


def errors(ws):
    ws["A1"], ws["A2"] = 10, 0
    ws["B1"], ws["B2"], ws["B3"] = "=A1/A2", "=B1*2", "=B2+1"


def clean(ws):
    ws["A1"], ws["A2"], ws["A3"] = 1, 2, "=SUM(A1:A2)"


def template(ws):
    ws["A1"], ws["B1"] = "Region", "Amount"
    chart = BarChart()
    chart.add_data(Reference(ws, min_col=2, min_row=1, max_row=4), titles_from_data=True)
    chart.set_categories(Reference(ws, min_col=1, min_row=2, max_row=4))
    ws.add_chart(chart, "H2")


for name, fn in [("noprefix", noprefix), ("cycle", cycle), ("badformat", badformat),
                 ("errors", errors), ("clean", clean), ("template", template)]:
    save(name, fn)
