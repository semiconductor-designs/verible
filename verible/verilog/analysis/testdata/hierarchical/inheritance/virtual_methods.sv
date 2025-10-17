// Virtual method override test
// Purpose: Test virtual methods and polymorphism

class Animal;
  string name;
  
  function new(string n);
    name = n;
  endfunction
  
  virtual function string make_sound();
    return "Some generic sound";
  endfunction
  
  virtual function void display();
    $display("%s says: %s", name, make_sound());
  endfunction
endclass

class Dog extends Animal;
  function new(string n);
    super.new(n);
  endfunction
  
  virtual function string make_sound();
    return "Woof!";
  endfunction
endclass

class Cat extends Animal;
  function new(string n);
    super.new(n);
  endfunction
  
  virtual function string make_sound();
    return "Meow!";
  endfunction
endclass

module test_polymorphism;
  initial begin
    Animal animals[3];
    
    animals[0] = new("Generic");
    animals[1] = Dog::new("Rex");
    animals[2] = Cat::new("Whiskers");
    
    foreach (animals[i]) begin
      animals[i].display();
    end
  end
endmodule

