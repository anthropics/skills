/**
 * Auto-redirect to the first link in the markdown.
 *
 * This is a workaround for mkdocs not supporting redirects in a way that doesn't have a huge-flash of content.
 */
class AutoRedirect extends HTMLElement {
    connectedCallback() {
        const currentUrl = window.location.href;
        const links = this.parentElement.closest(".md-content")?.querySelectorAll("a[href]") || [];
        // exclude links to github as those are edit links
        const link = Array.from(links).find(a => !a.href.includes("github.com"));

        if (link) {
            // immediately redirecting makes a flash of content, so do it after a second
            setTimeout(() => {
                if (currentUrl == window.location.href) {
                    window.location.replace(link.href);
                }
            }, 1000)
        }
    }
}

customElements.define('auto-redirect', AutoRedirect);