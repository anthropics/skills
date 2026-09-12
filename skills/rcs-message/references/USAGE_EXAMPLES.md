# RCS Message Skill - 使用示例

## 环境变量设置
```bash
export FIVE_G_APP_ID="your-app-id"
export FIVE_G_APP_SECRET="your-app-secret" 
export FIVE_G_SERVER_ROOT="https://api.your-5g-provider.com"
```

## 基本群发文本消息
```bash
python send.py -n "+8613900001234,+8613900002234" -m "您好，这是测试消息"
```

## 群发模板消息
```bash
python send.py --template-type RCS --template-id "269000000000000000" -n "+8613900001234,+8613900002234" --params "name:张三,amount:100"
```

## 带回落策略的模板消息
```bash
python send.py --template-type RCS --template-id "269000000000000000" -n "+8613900001234" --params "name:张三" --fallback-aim "149000000000000000:name:张三" --fallback-sms "短信回落内容"
```

## 从文件读取号码列表
```bash
python send.py -f phone_numbers.txt -m "批量发送消息"
```

## 配置文件方式
```bash
# 创建 config.json
{
    "server_root": "https://api.your-5g-provider.com",
    "default_fallback": {
        "aim_template_id": "149000000000000000",
        "sms_content": "短信回落内容"
    }
}

python send.py --config config.json -n "+8613900001234" -m "使用配置文件发送"
```

## 安全限制说明
- **号码数量限制**: 最多1000个号码
- **频率限制**: 默认每分钟最多10次请求
- **内容长度**: 文本消息最长1000字符
- **模板要求**: 模板必须通过审核才能使用

## 错误处理
脚本会自动处理以下情况：
- 环境变量缺失
- 号码格式错误
- 超出数量限制
- API认证失败
- 网络连接错误

## 调试模式
添加 `--debug` 参数查看详细请求信息：
```bash
python send.py -n "+8613900001234" -m "测试" --debug
```