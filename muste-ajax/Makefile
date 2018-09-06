.PHONY: hacky-sack/deploy/cse-principia

hacky-sack/deploy/cse-principia:
	ln -sf config/cse-principia.yaml config.yaml
	sed -i 's/VIRTUAL_ROOT = "\/"/VIRTUAL_ROOT = "\/mulle-dev\/"/' \
	  static/muste-gui.js
	stack install muste-ajax
	@echo "[New version installed]"
	@echo "Kill the old application with e.g.:"
	@echo ""
	@echo "    killall muste-ajax"
	@echo ""
	@echo "And run the new application with:"
	@echo ""
	@echo "    muste-ajax"
	@echo ""
	@echo "... recreating the database if necessary with:"
	@echo ""
	@echo "    db-init"
	@echo ""
