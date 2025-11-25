  - post meta
  - search replace
  - database
---

# WP-CLI Helper

## Content Management

### Create Content
```bash
# Create post
wp post create --post_title="My Post" --post_content="Content" --post_status=publish --allow-root

# Create page
wp post create --post_type=page --post_title="About Us" --post_status=publish --allow-root

# Create from file
wp post create ./content.html --post_title="My Page" --post_type=page --allow-root
```

### Update Content
```bash
wp post update 123 --post_content="New content" --allow-root
wp post update 123 --post_title="New Title" --allow-root
wp post update 123 --post_status=publish --allow-root
```

### List & Query
```bash
wp post list --post_type=page --format=table --allow-root
wp post list --post_status=draft --allow-root
wp post list --fields=ID,post_title,post_status --format=csv --allow-root
```

### Delete Content
```bash
wp post delete 123 --allow-root              # To trash
wp post delete 123 --force --allow-root      # Permanent
wp post delete $(wp post list --post_type=revision --format=ids) --allow-root  # All revisions
```

## Post Meta (Custom Fields)

### Get Meta
```bash
wp post meta get 123 _generate-full-width-content --allow-root
wp post meta list 123 --allow-root
```

### Set Meta
```bash
wp post meta update 123 _generate-full-width-content true --allow-root
wp post meta update 123 _generate-sidebar-layout-meta no-sidebar --allow-root
wp post meta update 123 _generate-disable-headline true --allow-root
```

### Delete Meta
```bash
wp post meta delete 123 old_custom_field --allow-root
```

## Database Operations

### Export & Import
```bash
wp db export backup-$(date +%Y%m%d).sql --allow-root
wp db import backup.sql --allow-root
```

### Search & Replace
```bash
wp search-replace 'http://oldsite.com' 'http://newsite.com' --allow-root
wp search-replace 'oldtext' 'newtext' --dry-run --allow-root      # Preview
wp search-replace 'old' 'new' wp_posts wp_postmeta --allow-root   # Specific tables
```

### Optimize
```bash
wp db optimize --allow-root
wp db check --allow-root
wp db repair --allow-root
wp db size --tables --format=table --allow-root
```

## Plugin Management

```bash
wp plugin install contact-form-7 --activate --allow-root
wp plugin list --status=active --allow-root
wp plugin update --all --allow-root
wp plugin deactivate plugin-name --allow-root
wp plugin delete plugin-name --allow-root
```

## Theme Management

```bash
wp theme install generatepress --activate --allow-root
wp theme list --allow-root
wp theme update generatepress --allow-root
```

## User Management

```bash
# Create
wp user create johndoe john@example.com --role=subscriber --user_pass=password --allow-root
wp user create admin admin@site.com --role=administrator --user_pass=SecurePass --allow-root

# Manage
wp user list --allow-root
wp user update 1 --user_pass=newpassword --allow-root
wp user set-role 1 editor --allow-root
wp user delete 123 --reassign=1 --allow-root
```

## Site Configuration

### Options
```bash
wp option get siteurl --allow-root
wp option update blogname "My Site" --allow-root
wp option update siteurl "http://localhost:8080" --allow-root
wp option update home "http://localhost:8080" --allow-root
```

### Rewrite Rules
```bash
wp rewrite flush --allow-root
wp rewrite structure '/%postname%/' --allow-root
```

### Cron
```bash
wp cron event list --allow-root
wp cron event run --all --allow-root
wp cron test --allow-root
```

## Media

```bash
wp media import image.jpg --title="My Image" --allow-root
wp media import image.jpg --post_id=123 --featured_image --allow-root
wp media regenerate --yes --allow-root
wp media regenerate --only-missing --yes --allow-root
```

## Cache

```bash
wp cache flush --allow-root
wp transient delete --all --allow-root
```

## Debug Mode

```bash
wp config set WP_DEBUG true --raw --allow-root
wp config set WP_DEBUG_LOG true --raw --allow-root
wp config set WP_DEBUG_DISPLAY false --raw --allow-root
```

## Common Patterns

### Setup Full-Width Page
```bash
PAGEID=57
wp post meta update $PAGEID _generate-full-width-content true --allow-root
wp post meta update $PAGEID _generate-sidebar-layout-meta no-sidebar --allow-root
wp post meta update $PAGEID _generate-disable-headline true --allow-root
```

### Clean Development Database
```bash
wp post delete 1 --force --allow-root  # Hello World
wp post delete 2 --force --allow-root  # Sample Page
wp plugin delete hello akismet --allow-root
```

## Output Formats

```bash
--format=table    # Default table
--format=csv      # CSV export
--format=json     # JSON output
--format=ids      # IDs only (for piping)
--format=count    # Count only
```

## Docker Context

```bash
# All commands in Docker
docker exec wordpress wp COMMAND --allow-root

# Example
docker exec wordpress wp post list --allow-root
```

## Performance Tips

1. Use `--format=ids` for batch operations
2. Use `--skip-plugins` to bypass plugin loading
3. Use `--dry-run` before destructive operations
4. Use `--quiet` to suppress output
