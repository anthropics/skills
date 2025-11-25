
# WordPress Docker Commands

## Container Management

### Start/Stop
```bash
docker-compose up -d              # Start all (detached)
docker-compose down               # Stop all
docker-compose restart            # Restart all
docker-compose stop               # Stop (keep volumes)
docker-compose down -v            # Stop + remove volumes (DESTRUCTIVE!)
```

### Status
```bash
docker-compose ps                 # List containers
docker stats                      # Resource usage
docker-compose logs -f wordpress  # Follow logs
```

## Container Access

```bash
# Enter container shell
docker exec -it wordpress bash

# Run single command
docker exec wordpress wp plugin list --allow-root

# Check versions
docker exec wordpress wp core version --allow-root
docker exec wordpress php -v
```

## Database Operations

### Backup
```bash
# Using WP-CLI
docker exec wordpress wp db export /tmp/backup.sql --allow-root
docker cp wordpress:/tmp/backup.sql ./backup.sql

# Using mysqldump
docker exec mysql mysqldump -u root -pPASSWORD wordpress > backup.sql
```

### Restore
```bash
docker cp ./backup.sql wordpress:/tmp/backup.sql
docker exec wordpress wp db import /tmp/backup.sql --allow-root
```

### Search-Replace URLs
```bash
docker exec wordpress wp search-replace 'http://oldsite.com' 'http://localhost:8080' --allow-root
```

### Optimize
```bash
docker exec wordpress wp db optimize --allow-root
docker exec wordpress wp db check --allow-root
```

## File Operations

```bash
# Copy TO container
docker cp ./local-file.php wordpress:/var/www/html/wp-content/themes/

# Copy FROM container
docker cp wordpress:/var/www/html/wp-config.php ./wp-config-backup.php

# Fix permissions
docker exec wordpress chown -R www-data:www-data /var/www/html
docker exec wordpress chmod -R 755 /var/www/html/wp-content/uploads
```

## WordPress Operations

### Plugins
```bash
docker exec wordpress wp plugin install contact-form-7 --activate --allow-root
docker exec wordpress wp plugin list --status=active --allow-root
docker exec wordpress wp plugin update --all --allow-root
```

### Themes
```bash
docker exec wordpress wp theme install generatepress --activate --allow-root
docker exec wordpress wp theme list --allow-root
```

### Users
```bash
docker exec wordpress wp user create admin admin@example.com --role=administrator --user_pass=password --allow-root
docker exec wordpress wp user update admin --user_pass=newpassword --allow-root
```

### Cache
```bash
docker exec wordpress wp cache flush --allow-root
docker exec wordpress wp rewrite flush --allow-root
docker exec wordpress wp transient delete --all --allow-root
```

## Logs & Debugging

```bash
docker-compose logs --tail=100 wordpress    # Last 100 lines
docker exec wordpress tail -f /var/log/apache2/error.log
docker inspect wordpress | grep -A 10 Health
```

## Troubleshooting

### Container Won't Start
```bash
docker-compose logs wordpress           # Check errors
docker-compose config                   # Verify syntax
lsof -i :8080                          # Check port conflicts
```

### Database Connection Issues
```bash
docker exec wordpress wp db check --allow-root
docker-compose ps mysql
docker-compose logs mysql
```

### Permission Issues
```bash
docker exec wordpress chown -R www-data:www-data /var/www/html
docker exec wordpress ls -la /var/www/html/wp-content
```

## Cleanup
```bash
docker container prune                  # Remove stopped containers
docker image prune -a                   # Remove unused images
docker volume prune                     # Remove unused volumes
docker system prune -a --volumes        # Full cleanup (CAREFUL!)
```

## Important Paths
- **WordPress root**: `/var/www/html`
- **Themes**: `/var/www/html/wp-content/themes`
- **Plugins**: `/var/www/html/wp-content/plugins`
- **Uploads**: `/var/www/html/wp-content/uploads`

## Pro Tips
1. Always use `--allow-root` for WP-CLI in Docker
2. Use `-d` flag for detached mode
3. Check logs first when troubleshooting
4. Backup before destructive operations
