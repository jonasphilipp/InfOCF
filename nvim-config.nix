
# nvim-config.nix
{ pkgs }:

{

  nvimDependencies = with pkgs; [
    nodejs
    tree-sitter
    ripgrep
    ranger
    (ruby.withPackages (ps: with ps; [ neovim ]))
  ];

  nvimEnvSetup = ''
		pip install pynvim neovim

    # Load Zsh configuration
    if [ -f ~/.zshrc ]; then
			exec zsh -i
    else
      echo "Warning: ~/.zshrc not found. Falling back to default shell."
    fi
  '';
}
