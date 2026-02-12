"""
Eval Logger - Automatic Training Data Generation
NO subprocesses. Pure Python. SQLite storage.
"""
import sqlite3
import json
from datetime import datetime
from pathlib import Path

class EvalLogger:
    def __init__(self, db_path="data/eval_log.db"):
        self.db_path = Path(db_path)
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self.conn = sqlite3.connect(str(self.db_path))
        self.create_tables()

    def create_tables(self):
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS eval_log (
                id INTEGER PRIMARY KEY,
                epoch_ms INTEGER,
                model_id TEXT,
                prompt TEXT,
                response TEXT,
                route INTEGER,
                validation_result TEXT,
                learned_pattern TEXT,
                timestamp TEXT
            )
        """)
        self.conn.commit()

    def log_exchange(self, model_id, prompt, response, route, validation=None):
        """Log a single model exchange"""
        epoch_ms = int(datetime.now().timestamp() * 1000)
        self.conn.execute("""
            INSERT INTO eval_log
            (epoch_ms, model_id, prompt, response, route, validation_result, timestamp)
            VALUES (?, ?, ?, ?, ?, ?, ?)
        """, (epoch_ms, model_id, prompt, response, route,
              json.dumps(validation) if validation else None, 
              datetime.now().isoformat()))
        self.conn.commit()

    def export_training_pairs(self, output_file="training_data.jsonl"):
        """Export successful exchanges as training pairs"""
        cursor = self.conn.execute("""
            SELECT prompt, response, validation_result
            FROM eval_log
            WHERE validation_result LIKE '%success%'
               OR validation_result LIKE '%pass%'
            ORDER BY epoch_ms
        """)

        with open(output_file, 'w') as f:
            for row in cursor:
                training_pair = {
                    "prompt": row[0],
                    "response": row[1],
                    "metadata": json.loads(row[2]) if row[2] else {}
                }
                f.write(json.dumps(training_pair) + "\n")
        
        return output_file

    def get_recent_exchanges(self, model_id=None, limit=50):
        """Get recent exchanges for reflection"""
        if model_id:
            cursor = self.conn.execute("""
                SELECT epoch_ms, model_id, prompt, response, route, validation_result
                FROM eval_log
                WHERE model_id = ?
                ORDER BY epoch_ms DESC
                LIMIT ?
            """, (model_id, limit))
        else:
            cursor = self.conn.execute("""
                SELECT epoch_ms, model_id, prompt, response, route, validation_result
                FROM eval_log
                ORDER BY epoch_ms DESC
                LIMIT ?
            """, (limit,))
        
        return [dict(zip(['epoch_ms', 'model_id', 'prompt', 'response', 'route', 'validation'], row)) 
                for row in cursor]

    def close(self):
        self.conn.close()


if __name__ == "__main__":
    # Test
    logger = EvalLogger("test_eval_log.db")
    logger.log_exchange(
        model_id="test_worker",
        prompt="Analyze UID 1224",
        response="This evidence shows malicious prosecution...",
        route=3,
        validation={"status": "success", "score": 0.85}
    )
    print("Logged test exchange")
    print("Recent:", logger.get_recent_exchanges(limit=5))
    logger.close()
