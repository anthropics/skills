# GenerateBlocks Query Loop Patterns

## Basic Post Grid

```html
<!-- wp:generateblocks/query-loop {"uniqueId":"posts-grid","postType":"post","postsPerPage":6,"columns":3,"columnsTablet":2,"columnsMobile":1,"horizontalGap":"30px","verticalGap":"30px"} -->
<div class="gb-query-loop gb-query-loop-posts-grid">

    <!-- wp:generateblocks/loop-item {"uniqueId":"post-card"} -->
    <article class="gb-loop-item">

        <!-- Featured Image -->
        <!-- wp:generateblocks/image {"uniqueId":"post-img","useDynamicData":true,"dynamicContentType":"featured-image","sizeSlug":"medium_large"} -->
        <figure class="gb-image gb-image-post-img">
            {{featured_image}}
        </figure>
        <!-- /wp:generateblocks/image -->

        <!-- Content Container -->
        <!-- wp:generateblocks/container {"uniqueId":"post-content","paddingTop":"20px"} -->
        <div class="gb-container">

            <!-- Category -->
            <!-- wp:generateblocks/headline {"uniqueId":"post-cat","element":"span","fontSize":"12px","textTransform":"uppercase","dynamicContentType":"post-terms","termSource":"category"} -->
            <span class="gb-headline">{{post_terms source="category"}}</span>
            <!-- /wp:generateblocks/headline -->

            <!-- Title -->
            <!-- wp:generateblocks/headline {"uniqueId":"post-title","element":"h3","dynamicContentType":"post-title","dynamicLinkType":"post-url"} -->
            <h3 class="gb-headline"><a href="{{post_url}}">{{post_title}}</a></h3>
            <!-- /wp:generateblocks/headline -->

            <!-- Excerpt -->
            <!-- wp:generateblocks/headline {"uniqueId":"post-excerpt","element":"p","dynamicContentType":"post-excerpt"} -->
            <p class="gb-headline">{{post_excerpt}}</p>
            <!-- /wp:generateblocks/headline -->

            <!-- Meta -->
            <!-- wp:generateblocks/container {"uniqueId":"post-meta","isGrid":true,"alignItems":"center","columnGap":"10px"} -->
            <div class="gb-container">
                <!-- wp:generateblocks/headline {"uniqueId":"post-date","element":"span","fontSize":"14px","dynamicContentType":"post-date"} -->
                <span class="gb-headline">{{post_date}}</span>
                <!-- /wp:generateblocks/headline -->
                <!-- wp:generateblocks/headline {"uniqueId":"post-author","element":"span","fontSize":"14px","dynamicContentType":"post-author"} -->
                <span class="gb-headline">by {{post_author}}</span>
                <!-- /wp:generateblocks/headline -->
            </div>
            <!-- /wp:generateblocks/container -->

        </div>
        <!-- /wp:generateblocks/container -->

    </article>
    <!-- /wp:generateblocks/loop-item -->

</div>
<!-- /wp:generateblocks/query-loop -->
```

## Featured Posts Slider

```html
<!-- wp:generateblocks/query-loop {"uniqueId":"featured-slider","postType":"post","postsPerPage":5,"stickyPosts":"only","columns":1} -->
<div class="gb-query-loop featured-slider">

    <!-- wp:generateblocks/loop-item {"uniqueId":"slide-item"} -->
    <div class="gb-loop-item slide">

        <!-- Background Image Container -->
        <!-- wp:generateblocks/container {"uniqueId":"slide-bg","minHeight":"500px","minHeightMobile":"300px","verticalAlignment":"flex-end","bgImageDynamic":true,"paddingTop":"60px","paddingBottom":"60px","paddingLeft":"40px","paddingRight":"40px"} -->
        <div class="gb-container">

            <!-- Overlay -->
            <!-- wp:generateblocks/container {"uniqueId":"slide-overlay","backgroundColor":"rgba(0,0,0,0.5)","position":"absolute","top":"0","left":"0","width":"100%","height":"100%"} -->
            <div class="gb-container"></div>
            <!-- /wp:generateblocks/container -->

            <!-- Content -->
            <!-- wp:generateblocks/container {"uniqueId":"slide-content","width":"600px","widthMobile":"100%","position":"relative","zIndex":"1"} -->
            <div class="gb-container">

                <!-- wp:generateblocks/headline {"uniqueId":"slide-title","element":"h2","textColor":"#ffffff","fontSize":"42px","fontSizeMobile":"28px","dynamicContentType":"post-title","dynamicLinkType":"post-url"} -->
                <h2 class="gb-headline"><a href="{{post_url}}">{{post_title}}</a></h2>
                <!-- /wp:generateblocks/headline -->

                <!-- wp:generateblocks/button-container {"uniqueId":"slide-btns"} -->
                <div class="gb-button-wrapper">
                    <!-- wp:generateblocks/button {"uniqueId":"slide-btn","backgroundColor":"#ffffff","textColor":"#000000","dynamicLinkType":"post-url"} -->
                    <a class="gb-button" href="{{post_url}}">Read More</a>
                    <!-- /wp:generateblocks/button -->
                </div>
                <!-- /wp:generateblocks/button-container -->

            </div>
            <!-- /wp:generateblocks/container -->

        </div>
        <!-- /wp:generateblocks/container -->

    </div>
    <!-- /wp:generateblocks/loop-item -->

</div>
<!-- /wp:generateblocks/query-loop -->
```

## Team Members Grid

```html
<!-- wp:generateblocks/query-loop {"uniqueId":"team-grid","postType":"team_member","postsPerPage":-1,"columns":4,"columnsTablet":2,"columnsMobile":1,"horizontalGap":"30px","verticalGap":"40px"} -->
<div class="gb-query-loop team-grid">

    <!-- wp:generateblocks/loop-item {"uniqueId":"team-card"} -->
    <div class="gb-loop-item team-card">

        <!-- Photo -->
        <!-- wp:generateblocks/image {"uniqueId":"team-photo","useDynamicData":true,"dynamicContentType":"featured-image","borderRadius":"50%","width":"200px","height":"200px","objectFit":"cover","marginLeft":"auto","marginRight":"auto"} -->
        <figure class="gb-image">{{featured_image}}</figure>
        <!-- /wp:generateblocks/image -->

        <!-- Name -->
        <!-- wp:generateblocks/headline {"uniqueId":"team-name","element":"h3","textAlign":"center","marginTop":"20px","marginBottom":"5px","dynamicContentType":"post-title"} -->
        <h3 class="gb-headline">{{post_title}}</h3>
        <!-- /wp:generateblocks/headline -->

        <!-- Position (ACF Field) -->
        <!-- wp:generateblocks/headline {"uniqueId":"team-position","element":"p","textAlign":"center","textColor":"#666666","fontSize":"14px","textTransform":"uppercase","letterSpacing":"1px","dynamicContentType":"acf","acfField":"position"} -->
        <p class="gb-headline">{{acf field="position"}}</p>
        <!-- /wp:generateblocks/headline -->

        <!-- Bio -->
        <!-- wp:generateblocks/headline {"uniqueId":"team-bio","element":"p","textAlign":"center","marginTop":"15px","dynamicContentType":"post-excerpt"} -->
        <p class="gb-headline">{{post_excerpt}}</p>
        <!-- /wp:generateblocks/headline -->

        <!-- Social Links -->
        <!-- wp:generateblocks/container {"uniqueId":"team-social","isGrid":true,"justifyContent":"center","columnGap":"15px","marginTop":"15px"} -->
        <div class="gb-container social-links">
            <!-- Social icons here -->
        </div>
        <!-- /wp:generateblocks/container -->

    </div>
    <!-- /wp:generateblocks/loop-item -->

</div>
<!-- /wp:generateblocks/query-loop -->
```

## Product Showcase (WooCommerce)

```html
<!-- wp:generateblocks/query-loop {"uniqueId":"products","postType":"product","postsPerPage":8,"columns":4,"columnsTablet":2,"columnsMobile":2,"horizontalGap":"20px","verticalGap":"30px","taxQuery":[{"taxonomy":"product_cat","terms":["featured"],"field":"slug"}]} -->
<div class="gb-query-loop products-grid">

    <!-- wp:generateblocks/loop-item {"uniqueId":"product-card"} -->
    <div class="gb-loop-item product-card">

        <!-- Product Image -->
        <!-- wp:generateblocks/container {"uniqueId":"product-img-wrap","position":"relative","overflow":"hidden"} -->
        <div class="gb-container">
            <!-- wp:generateblocks/image {"uniqueId":"product-img","useDynamicData":true,"dynamicContentType":"featured-image","dynamicLinkType":"post-url"} -->
            <figure class="gb-image">
                <a href="{{post_url}}">{{featured_image}}</a>
            </figure>
            <!-- /wp:generateblocks/image -->

            <!-- Sale Badge -->
            <!-- wp:generateblocks/container {"uniqueId":"sale-badge","position":"absolute","top":"10px","right":"10px","backgroundColor":"#e74c3c","paddingTop":"5px","paddingRight":"10px","paddingBottom":"5px","paddingLeft":"10px","borderRadius":"3px"} -->
            <div class="gb-container sale-badge">
                <!-- wp:generateblocks/headline {"uniqueId":"sale-text","element":"span","textColor":"#ffffff","fontSize":"12px","fontWeight":"bold"} -->
                <span class="gb-headline">SALE</span>
                <!-- /wp:generateblocks/headline -->
            </div>
            <!-- /wp:generateblocks/container -->
        </div>
        <!-- /wp:generateblocks/container -->

        <!-- Product Info -->
        <!-- wp:generateblocks/container {"uniqueId":"product-info","paddingTop":"15px"} -->
        <div class="gb-container">

            <!-- Category -->
            <!-- wp:generateblocks/headline {"uniqueId":"product-cat","element":"span","fontSize":"12px","textColor":"#888888","dynamicContentType":"post-terms","termSource":"product_cat"} -->
            <span class="gb-headline">{{post_terms source="product_cat"}}</span>
            <!-- /wp:generateblocks/headline -->

            <!-- Title -->
            <!-- wp:generateblocks/headline {"uniqueId":"product-title","element":"h3","fontSize":"16px","marginTop":"5px","marginBottom":"10px","dynamicContentType":"post-title","dynamicLinkType":"post-url"} -->
            <h3 class="gb-headline"><a href="{{post_url}}">{{post_title}}</a></h3>
            <!-- /wp:generateblocks/headline -->

            <!-- Price (Custom Field) -->
            <!-- wp:generateblocks/headline {"uniqueId":"product-price","element":"span","fontSize":"18px","fontWeight":"bold","textColor":"#333333","dynamicContentType":"post-meta","metaKey":"_price"} -->
            <span class="gb-headline">${{post_meta meta_key="_price"}}</span>
            <!-- /wp:generateblocks/headline -->

        </div>
        <!-- /wp:generateblocks/container -->

    </div>
    <!-- /wp:generateblocks/loop-item -->

</div>
<!-- /wp:generateblocks/query-loop -->
```

## Related Posts

```html
<!-- wp:generateblocks/query-loop {"uniqueId":"related-posts","postType":"post","postsPerPage":3,"excludeCurrent":true,"columns":3,"columnsTablet":2,"columnsMobile":1,"horizontalGap":"30px","taxQueryRelation":"category"} -->
<div class="gb-query-loop related-posts">

    <!-- Section Title -->
    <!-- wp:generateblocks/headline {"uniqueId":"related-title","element":"h2","marginBottom":"30px"} -->
    <h2 class="gb-headline">Related Posts</h2>
    <!-- /wp:generateblocks/headline -->

    <!-- wp:generateblocks/loop-item {"uniqueId":"related-item"} -->
    <article class="gb-loop-item">

        <!-- wp:generateblocks/container {"uniqueId":"related-card","isGrid":true,"flexDirection":"column"} -->
        <div class="gb-container">

            <!-- wp:generateblocks/image {"uniqueId":"related-img","useDynamicData":true,"dynamicContentType":"featured-image","sizeSlug":"medium","dynamicLinkType":"post-url"} -->
            <figure class="gb-image">
                <a href="{{post_url}}">{{featured_image}}</a>
            </figure>
            <!-- /wp:generateblocks/image -->

            <!-- wp:generateblocks/headline {"uniqueId":"related-post-title","element":"h4","marginTop":"15px","dynamicContentType":"post-title","dynamicLinkType":"post-url"} -->
            <h4 class="gb-headline"><a href="{{post_url}}">{{post_title}}</a></h4>
            <!-- /wp:generateblocks/headline -->

            <!-- wp:generateblocks/headline {"uniqueId":"related-date","element":"span","fontSize":"14px","textColor":"#888888","dynamicContentType":"post-date"} -->
            <span class="gb-headline">{{post_date}}</span>
            <!-- /wp:generateblocks/headline -->

        </div>
        <!-- /wp:generateblocks/container -->

    </article>
    <!-- /wp:generateblocks/loop-item -->

</div>
<!-- /wp:generateblocks/query-loop -->
```

## Testimonials Carousel

```html
<!-- wp:generateblocks/query-loop {"uniqueId":"testimonials","postType":"testimonial","postsPerPage":-1,"columns":1,"className":"testimonials-carousel"} -->
<div class="gb-query-loop testimonials-carousel">

    <!-- wp:generateblocks/loop-item {"uniqueId":"testimonial-item"} -->
    <div class="gb-loop-item testimonial-slide">

        <!-- wp:generateblocks/container {"uniqueId":"testimonial-card","backgroundColor":"#f9f9f9","paddingTop":"40px","paddingRight":"40px","paddingBottom":"40px","paddingLeft":"40px","borderRadius":"8px","textAlign":"center"} -->
        <div class="gb-container">

            <!-- Quote Icon -->
            <!-- wp:generateblocks/headline {"uniqueId":"quote-icon","element":"span","fontSize":"48px","textColor":"#0073aa","marginBottom":"20px"} -->
            <span class="gb-headline">"</span>
            <!-- /wp:generateblocks/headline -->

            <!-- Testimonial Content -->
            <!-- wp:generateblocks/headline {"uniqueId":"testimonial-content","element":"p","fontSize":"18px","lineHeight":"1.8","fontStyle":"italic","dynamicContentType":"post-content"} -->
            <p class="gb-headline">{{post_content}}</p>
            <!-- /wp:generateblocks/headline -->

            <!-- Author Info -->
            <!-- wp:generateblocks/container {"uniqueId":"testimonial-author","isGrid":true,"justifyContent":"center","alignItems":"center","columnGap":"15px","marginTop":"30px"} -->
            <div class="gb-container">

                <!-- wp:generateblocks/image {"uniqueId":"testimonial-avatar","useDynamicData":true,"dynamicContentType":"featured-image","width":"60px","height":"60px","borderRadius":"50%","objectFit":"cover"} -->
                <figure class="gb-image">{{featured_image}}</figure>
                <!-- /wp:generateblocks/image -->

                <!-- wp:generateblocks/container {"uniqueId":"author-details","textAlign":"left"} -->
                <div class="gb-container">
                    <!-- wp:generateblocks/headline {"uniqueId":"author-name","element":"strong","dynamicContentType":"post-title"} -->
                    <strong class="gb-headline">{{post_title}}</strong>
                    <!-- /wp:generateblocks/headline -->
                    <!-- wp:generateblocks/headline {"uniqueId":"author-role","element":"span","fontSize":"14px","textColor":"#666666","dynamicContentType":"acf","acfField":"role"} -->
                    <span class="gb-headline">{{acf field="role"}}</span>
                    <!-- /wp:generateblocks/headline -->
                </div>
                <!-- /wp:generateblocks/container -->

            </div>
            <!-- /wp:generateblocks/container -->

        </div>
        <!-- /wp:generateblocks/container -->

    </div>
    <!-- /wp:generateblocks/loop-item -->

</div>
<!-- /wp:generateblocks/query-loop -->
```

## Query with Pagination

```html
<!-- wp:generateblocks/query-loop {"uniqueId":"paginated-posts","postType":"post","postsPerPage":12,"columns":3,"columnsTablet":2,"columnsMobile":1,"horizontalGap":"30px","verticalGap":"30px","pagination":true,"paginationType":"numbers"} -->
<div class="gb-query-loop paginated-posts">

    <!-- Loop items here -->
    <!-- wp:generateblocks/loop-item {"uniqueId":"post-item"} -->
    <article class="gb-loop-item">
        <!-- Post content blocks -->
    </article>
    <!-- /wp:generateblocks/loop-item -->

    <!-- Pagination automatically added by GB Pro -->

</div>
<!-- /wp:generateblocks/query-loop -->
```

## CSS for Query Patterns

```css
/* Post Grid Hover Effects */
.gb-query-loop .gb-loop-item {
    transition: transform 0.3s ease, box-shadow 0.3s ease;
}

.gb-query-loop .gb-loop-item:hover {
    transform: translateY(-5px);
    box-shadow: 0 10px 30px rgba(0,0,0,0.1);
}

/* Testimonials Carousel */
.testimonials-carousel {
    position: relative;
    overflow: hidden;
}

.testimonials-carousel .gb-loop-item {
    opacity: 0;
    position: absolute;
    top: 0;
    left: 0;
    width: 100%;
    transition: opacity 0.5s ease;
}

.testimonials-carousel .gb-loop-item.active {
    opacity: 1;
    position: relative;
}

/* Product Grid */
.products-grid .product-card .gb-image img {
    transition: transform 0.3s ease;
}

.products-grid .product-card:hover .gb-image img {
    transform: scale(1.05);
}

/* Pagination Styling */
.gb-query-loop-pagination {
    display: flex;
    justify-content: center;
    gap: 10px;
    margin-top: 40px;
}

.gb-query-loop-pagination a {
    padding: 10px 15px;
    background: #f0f0f0;
    border-radius: 4px;
    transition: background 0.3s ease;
}

.gb-query-loop-pagination a:hover,
.gb-query-loop-pagination .current {
    background: #0073aa;
    color: #fff;
}
```
