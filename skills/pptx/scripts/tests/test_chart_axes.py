import unittest

from office.helpers.pptx_chart import find_chart_problems


def chart_with_third_axis(axis_id):
    xml = (
        '<c:chartSpace xmlns:c="http://schemas.openxmlformats.org/drawingml/2006/chart">'
        '<c:line3DChart><c:axId val="1"/><c:axId val="2"/>'
        f'<c:axId val="{axis_id}"/></c:line3DChart>'
        '<c:catAx><c:axId val="1"/></c:catAx>'
        '<c:valAx><c:axId val="2"/></c:valAx>'
        '<c:serAx><c:axId val="3"/></c:serAx>'
        '</c:chartSpace>'
    )
    return {"ppt/charts/chart1.xml": xml.encode()}


class ChartAxisTests(unittest.TestCase):
    def test_line_3d_chart_reports_missing_third_axis(self):
        problems = find_chart_problems(chart_with_third_axis(999))
        self.assertTrue(any("999" in problem for problem in problems), problems)

    def test_line_3d_chart_accepts_three_live_axes(self):
        self.assertEqual(find_chart_problems(chart_with_third_axis(3)), [])

    def test_line_3d_chart_rejects_repeated_axis_reference(self):
        problems = find_chart_problems(chart_with_third_axis(1))
        self.assertTrue(problems)


if __name__ == "__main__":
    unittest.main()
