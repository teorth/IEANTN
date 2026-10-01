from test_ieantn import FixtureRepo, ieantn


class TestReceiptOwnStatement(FixtureRepo):
    def test_receipt_must_record_its_own_statement(self):
        for statement in (None, {}, {'B.v1.main': 'b'}):
            with self.subTest(statement=statement):
                receipt = {'environment': ieantn.current_environment()}
                if statement is not None:
                    receipt['statement'] = statement
                light, detail = ieantn.assess(
                    'A.v1.main', receipt, {'A.v1.main': 'a', 'B.v1.main': 'b'})
                self.assertEqual(light, 'BROKEN')
                self.assertIn('A.v1.main', detail)
