import sys
import os
import abc
import io
import contextlib
import collections
from collections import defaultdict
import collections.abc
import copy
from functools import lru_cache
import importlib
import inspect
import pickle
import re
import subprocess
import tempfile
import textwrap
import types
from pathlib import Path
from unittest import TestCase, main, skipUnless, skipIf
from unittest.mock import patch
import typing
from typing import Optional, Union, AnyStr
from typing import T, KT, VT  # Not in __all__.
from typing import Tuple, List, Set, Dict, Iterable, Iterator, Callable
from typing import Generic
from typing import no_type_check
import warnings

import typing_extensions
from typing_extensions import NoReturn, Any, ClassVar, Final, IntVar, Literal, Type, NewType, TypedDict, Self
from typing_extensions import TypeAlias, ParamSpec, Concatenate, ParamSpecArgs, ParamSpecKwargs, TypeGuard
from typing_extensions import Awaitable, AsyncIterator, AsyncContextManager, Required, NotRequired
from typing_extensions import Protocol, runtime, runtime_checkable, Annotated, final, is_typeddict
from typing_extensions import TypeVarTuple, Unpack, dataclass_transform, reveal_type, Never, assert_never, LiteralString
from typing_extensions import assert_type, get_type_hints, get_origin, get_args, get_original_bases
from typing_extensions import clear_overloads, get_overloads, overload
from typing_extensions import NamedTuple
from typing_extensions import override, deprecated, Buffer, TypeAliasType, TypeVar
from _typed_dict_test_helper import Foo, FooGeneric

# Flags used to mark tests that only apply after a specific
# version of the typing module.
TYPING_3_8_0 = sys.version_info[:3] >= (3, 8, 0)
TYPING_3_9_0 = sys.version_info[:3] >= (3, 9, 0)
TYPING_3_10_0 = sys.version_info[:3] >= (3, 10, 0)

# 3.11 makes runtime type checks (_type_check) more lenient.
TYPING_3_11_0 = sys.version_info[:3] >= (3, 11, 0)

# 3.12 changes the representation of Unpack[] (PEP 692)
TYPING_3_12_0 = sys.version_info[:3] >= (3, 12, 0)

# https://github.com/python/cpython/pull/27017 was backported into some 3.9 and 3.10
# versions, but not all
HAS_FORWARD_MODULE = "module" in inspect.signature(typing._type_check).parameters

ANN_MODULE_SOURCE = '''\
from typing import Optional
from functools import wraps

__annotations__[1] = 2

class C:

    x = 5; y: Optional['C'] = None

from typing import Tuple
x: int = 5; y: str = x; f: Tuple[int, int]

class M(type):

    __annotations__['123'] = 123
    o: type = object

(pars): bool = True

class D(C):
    j: str = 'hi'; k: str= 'bye'

from types import new_class
h_class = new_class('H', (C,))
j_class = new_class('J')

class F():
    z: int = 5
    def __init__(self, x):
        pass

class Y(F):
    def __init__(self):
        super(F, self).__init__(123)

class Meta(type):
    def __new__(meta, name, bases, namespace):
        return super().__new__(meta, name, bases, namespace)

class S(metaclass = Meta):
    x: str = 'something'
    y: str = 'something else'

def foo(x: int = 10):
    def bar(y: List[str]):
        x: str = 'yes'
    bar()

def dec(func):
    @wraps(func)
    def wrapper(*args, **kwargs):
        return func(*args, **kwargs)
    return wrapper
'''

ANN_MODULE_2_SOURCE = '''\
from typing import no_type_check, ClassVar

i: int = 1
j: int
x: float = i/10

def f():
    class C: ...
    return C()

f().new_attr: object = object()

class C:
    def __init__(self, x: int) -> None:
        self.x = x

c = C(5)
c.new_attr: int = 10

__annotations__ = {}


@no_type_check
class NTC:
    def meth(self, param: complex) -> None:
        ...

class CV:
    var: ClassVar['CV']

CV.var = CV()
'''

ANN_MODULE_3_SOURCE = '''\
def f_bad_ann():
    __annotations__[1] = 2

class C_OK:
    def __init__(self, x: int) -> None:
        self.x: no_such_name = x  # This one is OK as proposed by Guido

class D_bad_ann:
    def __init__(self, x: int) -> None:
        sfel.y: int = 0

def g_bad_ann():
    no_such_name.attr: int = 0
'''


class BaseTestCase(TestCase):
    def assertIsSubclass(self, cls, class_or_tuple, msg=None):
        if not issubclass(cls, class_or_tuple):
            message = f'{cls!r} is not a subclass of {repr(class_or_tuple)}'
            if msg is not None:
                message += f' : {msg}'
            raise self.failureException(message)

    def assertNotIsSubclass(self, cls, class_or_tuple, msg=None):
        if issubclass(cls, class_or_tuple):
            message = f'{cls!r} is a subclass of {repr(class_or_tuple)}'
            if msg is not None:
                message += f' : {msg}'
            raise self.failureException(message)


class Employee:
    pass


class BottomTypeTestsMixin:
    bottom_type: ClassVar[Any]

    def test_equality(self):
        self.assertEqual(self.bottom_type, self.bottom_type)
        self.assertIs(self.bottom_type, self.bottom_type)
        self.assertNotEqual(self.bottom_type, None)

    def test_get_origin(self):
        self.assertIs(get_origin(self.bottom_type), None)

    def test_instance_type_error(self):
        with self.assertRaises(TypeError):
            isinstance(42, self.bottom_type)

    def test_subclass_type_error(self):
        with self.assertRaises(TypeError):
            issubclass(Employee, self.bottom_type)
        with self.assertRaises(TypeError):
            issubclass(NoReturn, self.bottom_type)

    def test_not_generic(self):
        with self.assertRaises(TypeError):
            self.bottom_type[int]

    def test_cannot_subclass(self):
        with self.assertRaises(TypeError):
            class A(self.bottom_type):
                pass
        with self.assertRaises(TypeError):
            class A(type(self.bottom_type)):
                pass

    def test_cannot_instantiate(self):
        with self.assertRaises(TypeError):
            self.bottom_type()
        with self.assertRaises(TypeError):
            type(self.bottom_type)()

    def test_pickle(self):
        for proto in range(pickle.HIGHEST_PROTOCOL):
            pickled = pickle.dumps(self.bottom_type, protocol=proto)
            self.assertIs(self.bottom_type, pickle.loads(pickled))


class NoReturnTests(BottomTypeTestsMixin, BaseTestCase):
    bottom_type = NoReturn

    def test_repr(self):
        if hasattr(typing, 'NoReturn'):
            self.assertEqual(repr(NoReturn), 'typing.NoReturn')
        else:
            self.assertEqual(repr(NoReturn), 'typing_extensions.NoReturn')

    def test_get_type_hints(self):
        def some(arg: NoReturn) -> NoReturn: ...
        def some_str(arg: 'NoReturn') -> 'typing.NoReturn': ...

        expected = {'arg': NoReturn, 'return': NoReturn}
        targets = [some]

        # On 3.7.0 and 3.7.1, https://github.com/python/cpython/pull/10772
        # wasn't applied yet and NoReturn fails _type_check.
        if not ((3, 7, 0) <= sys.version_info < (3, 7, 2)):
            targets.append(some_str)
        for target in targets:
            with self.subTest(target=target):
                self.assertEqual(gth(target), expected)

    def test_not_equality(self):
        self.assertNotEqual(NoReturn, Never)
        self.assertNotEqual(Never, NoReturn)


class NeverTests(BottomTypeTestsMixin, BaseTestCase):
    bottom_type = Never

    def test_repr(self):
        if hasattr(typing, 'Never'):
            self.assertEqual(repr(Never), 'typing.Never')
        else:
            self.assertEqual(repr(Never), 'typing_extensions.Never')

    def test_get_type_hints(self):
        def some(arg: Never) -> Never: ...
        def some_str(arg: 'Never') -> 'typing_extensions.Never': ...

        expected = {'arg': Never, 'return': Never}
        for target in [some, some_str]:
            with self.subTest(target=target):
                self.assertEqual(gth(target), expected)


class AssertNeverTests(BaseTestCase):
    def test_exception(self):
        with self.assertRaises(AssertionError):
            assert_never(None)


class OverrideTests(BaseTestCase):
    def test_override(self):
        class Base:
            def normal_method(self): ...
            @staticmethod
            def static_method_good_order(): ...
            @staticmethod
            def static_method_bad_order(): ...
            @staticmethod
            def decorator_with_slots(): ...

        class Derived(Base):
            @override
            def normal_method(self):
                return 42

            @staticmethod
            @override
            def static_method_good_order():
                return 42

            @override
            @staticmethod
            def static_method_bad_order():
                return 42


        self.assertIsSubclass(Derived, Base)
        instance = Derived()
        self.assertEqual(instance.normal_method(), 42)
        self.assertIs(True, instance.normal_method.__override__)
        self.assertEqual(Derived.static_method_good_order(), 42)
        self.assertIs(True, Derived.static_method_good_order.__override__)
        self.assertEqual(Derived.static_method_bad_order(), 42)
        self.assertIs(False, hasattr(Derived.static_method_bad_order, "__override__"))


class DeprecatedTests(BaseTestCase):
    def test_dunder_deprecated(self):
        @deprecated("A will go away soon")
        class A:
            pass

        self.assertEqual(A.__deprecated__, "A will go away soon")
        self.assertIsInstance(A, type)

        @deprecated("b will go away soon")
        def b():
            pass

        self.assertEqual(b.__deprecated__, "b will go away soon")
        self.assertIsInstance(b, types.FunctionType)

        @overload
        @deprecated("no more ints")
        def h(x: int) -> int: ...
        @overload
        def h(x: str) -> str: ...
        def h(x):
            return x

        overloads = get_overloads(h)
        self.assertEqual(len(overloads), 2)
        self.assertEqual(overloads[0].__deprecated__, "no more ints")

    def test_class(self):
        @deprecated("A will go away soon")
        class A:
            pass

        with self.assertWarnsRegex(DeprecationWarning, "A will go away soon"):
            A()
        with self.assertWarnsRegex(DeprecationWarning, "A will go away soon"):
            with self.assertRaises(TypeError):
                A(42)

    def test_class_with_init(self):
        @deprecated("HasInit will go away soon")
        class HasInit:
            def __init__(self, x):
                self.x = x

        with self.assertWarnsRegex(DeprecationWarning, "HasInit will go away soon"):
            instance = HasInit(42)
        self.assertEqual(instance.x, 42)

    def test_class_with_new(self):
        has_new_called = False

        @deprecated("HasNew will go away soon")
        class HasNew:
            def __new__(cls, x):
                nonlocal has_new_called
                has_new_called = True
                return super().__new__(cls)

            def __init__(self, x) -> None:
                self.x = x

        with self.assertWarnsRegex(DeprecationWarning, "HasNew will go away soon"):
            instance = HasNew(42)
        self.assertEqual(instance.x, 42)
        self.assertTrue(has_new_called)

    def test_class_with_inherited_new(self):
        new_base_called = False

        class NewBase:
            def __new__(cls, x):
                nonlocal new_base_called
                new_base_called = True
                return super().__new__(cls)

            def __init__(self, x) -> None:
                self.x = x

        @deprecated("HasInheritedNew will go away soon")
        class HasInheritedNew(NewBase):
            pass

        with self.assertWarnsRegex(DeprecationWarning, "HasInheritedNew will go away soon"):
            instance = HasInheritedNew(42)
        self.assertEqual(instance.x, 42)
        self.assertTrue(new_base_called)

    def test_class_with_new_but_no_init(self):
        new_called = False

        @deprecated("HasNewNoInit will go away soon")
        class HasNewNoInit:
            def __new__(cls, x):
                nonlocal new_called
                new_called = True
                obj = super().__new__(cls)
                obj.x = x
                return obj

        with self.assertWarnsRegex(DeprecationWarning, "HasNewNoInit will go away soon"):
            instance = HasNewNoInit(42)
        self.assertEqual(instance.x, 42)
        self.assertTrue(new_called)

    def test_function(self):
        @deprecated("b will go away soon")
        def b():
            pass

        with self.assertWarnsRegex(DeprecationWarning, "b will go away soon"):
            b()

    def test_method(self):
        class Capybara:
            @deprecated("x will go away soon")
            def x(self):
                pass

        instance = Capybara()
        with self.assertWarnsRegex(DeprecationWarning, "x will go away soon"):
            instance.x()

    def test_property(self):
        class Capybara:
            @property
            @deprecated("x will go away soon")
            def x(self):
                pass

            @property
            def no_more_setting(self):
                return 42

            @no_more_setting.setter
            @deprecated("no more setting")
            def no_more_setting(self, value):
                pass

        instance = Capybara()
        with self.assertWarnsRegex(DeprecationWarning, "x will go away soon"):
            instance.x

        with warnings.catch_warnings():
            warnings.simplefilter("error")
            self.assertEqual(instance.no_more_setting, 42)

        with self.assertWarnsRegex(DeprecationWarning, "no more setting"):
            instance.no_more_setting = 42

    def test_category(self):
        @deprecated("c will go away soon", category=RuntimeWarning)
        def c():
            pass

        with self.assertWarnsRegex(RuntimeWarning, "c will go away soon"):
            c()

    def test_turn_off_warnings(self):
        @deprecated("d will go away soon", category=None)
        def d():
            pass

        with warnings.catch_warnings():
            warnings.simplefilter("error")
            d()


class AnyTests(BaseTestCase):
    def test_can_subclass(self):
        class Mock(Any): pass
        self.assertTrue(issubclass(Mock, Any))
        self.assertIsInstance(Mock(), Mock)

        class Something: pass
        self.assertFalse(issubclass(Something, Any))
        self.assertNotIsInstance(Something(), Mock)

        class MockSomething(Something, Mock): pass
        self.assertTrue(issubclass(MockSomething, Any))
        ms = MockSomething()
        self.assertIsInstance(ms, MockSomething)
        self.assertIsInstance(ms, Something)
        self.assertIsInstance(ms, Mock)

    class SubclassesAny(Any):
        ...

    def test_repr(self):
        if sys.version_info >= (3, 11):
            mod_name = 'typing'
        else:
            mod_name = 'typing_extensions'
        self.assertEqual(repr(Any), f"{mod_name}.Any")

    @skipIf(sys.version_info[:3] == (3, 11, 0), "A bug was fixed in 3.11.1")
    def test_repr_on_Any_subclass(self):
        self.assertEqual(
            repr(self.SubclassesAny),
            f"<class '{self.SubclassesAny.__module__}.AnyTests.SubclassesAny'>"
        )

    def test_instantiation(self):
        with self.assertRaises(TypeError):
            Any()

        self.SubclassesAny()

    def test_isinstance(self):
        with self.assertRaises(TypeError):
            isinstance(object(), Any)

        isinstance(object(), self.SubclassesAny)


class ClassVarTests(BaseTestCase):

    def test_basics(self):
        if not TYPING_3_11_0:
            with self.assertRaises(TypeError):
                ClassVar[1]
        with self.assertRaises(TypeError):
            ClassVar[int, str]
        with self.assertRaises(TypeError):
            ClassVar[int][str]

    def test_repr(self):
        if hasattr(typing, 'ClassVar'):
            mod_name = 'typing'
        else:
            mod_name = 'typing_extensions'
        self.assertEqual(repr(ClassVar), mod_name + '.ClassVar')
        cv = ClassVar[int]
        self.assertEqual(repr(cv), mod_name + '.ClassVar[int]')
        cv = ClassVar[Employee]
        self.assertEqual(repr(cv), mod_name + f'.ClassVar[{__name__}.Employee]')

    def test_cannot_subclass(self):
        with self.assertRaises(TypeError):
            class C(type(ClassVar)):
                pass
        with self.assertRaises(TypeError):
            class C(type(ClassVar[int])):
                pass

    def test_cannot_init(self):
        with self.assertRaises(TypeError):
            ClassVar()
        with self.assertRaises(TypeError):
            type(ClassVar)()
        with self.assertRaises(TypeError):
            type(ClassVar[Optional[int]])()

    def test_no_isinstance(self):
        with self.assertRaises(TypeError):
            isinstance(1, ClassVar[int])
        with self.assertRaises(TypeError):
            issubclass(int, ClassVar)


class FinalTests(BaseTestCase):

    def test_basics(self):
        if not TYPING_3_11_0:
            with self.assertRaises(TypeError):
                Final[1]
        with self.assertRaises(TypeError):
            Final[int, str]
        with self.assertRaises(TypeError):
            Final[int][str]

    def test_repr(self):
        if hasattr(typing, 'Final') and sys.version_info[:2] >= (3, 7):
            mod_name = 'typing'
        else:
            mod_name = 'typing_extensions'
        self.assertEqual(repr(Final), mod_name + '.Final')
        cv = Final[int]
        self.assertEqual(repr(cv), mod_name + '.Final[int]')
        cv = Final[Employee]
        self.assertEqual(repr(cv), mod_name + f'.Final[{__name__}.Employee]')

    def test_cannot_subclass(self):
        with self.assertRaises(TypeError):
            class C(type(Final)):
                pass
        with self.assertRaises(TypeError):
            class C(type(Final[int])):
                pass

    def test_cannot_init(self):
        with self.assertRaises(TypeError):
            Final()
        with self.assertRaises(TypeError):
            type(Final)()
        with self.assertRaises(TypeError):
            type(Final[Optional[int]])()

    def test_no_isinstance(self):
        with self.assertRaises(TypeError):
            isinstance(1, Final[int])
        with self.assertRaises(TypeError):
            issubclass(int, Final)


class RequiredTests(BaseTestCase):

    def test_basics(self):
        if not TYPING_3_11_0:
            with self.assertRaises(TypeError):
                Required[1]
        with self.assertRaises(TypeError):
            Required[int, str]
        with self.assertRaises(TypeError):
            Required[int][str]

    def test_repr(self):
        if hasattr(typing, 'Required'):
            mod_name = 'typing'
        else:
            mod_name = 'typing_extensions'
        self.assertEqual(repr(Required), mod_name + '.Required')
        cv = Required[int]
        self.assertEqual(repr(cv), mod_name + '.Required[int]')
        cv = Required[Employee]
        self.assertEqual(repr(cv), mod_name + '.Required[%s.Employee]' % __name__)

    def test_cannot_subclass(self):
        with self.assertRaises(TypeError):
            class C(type(Required)):
                pass
        with self.assertRaises(TypeError):
            class C(type(Required[int])):
                pass

    def test_cannot_init(self):
        with self.assertRaises(TypeError):
            Required()
        with self.assertRaises(TypeError):
            type(Required)()
        with self.assertRaises(TypeError):
            type(Required[Optional[int]])()

    def test_no_isinstance(self):
        with self.assertRaises(TypeError):
            isinstance(1, Required[int])
        with self.assertRaises(TypeError):
            issubclass(int, Required)


class NotRequiredTests(BaseTestCase):

    def test_basics(self):
        if not TYPING_3_11_0:
            with self.assertRaises(TypeError):
                NotRequired[1]
        with self.assertRaises(TypeError):
            NotRequired[int, str]
        with self.assertRaises(TypeError):
            NotRequired[int][str]

    def test_repr(self):
        if hasattr(typing, 'NotRequired'):
            mod_name = 'typing'
        else:
            mod_name = 'typing_extensions'
        self.assertEqual(repr(NotRequired), mod_name + '.NotRequired')
        cv = NotRequired[int]
        self.assertEqual(repr(cv), mod_name + '.NotRequired[int]')
        cv = NotRequired[Employee]
        self.assertEqual(repr(cv), mod_name + '.NotRequired[%s.Employee]' % __name__)

    def test_cannot_subclass(self):
        with self.assertRaises(TypeError):
            class C(type(NotRequired)):
                pass
        with self.assertRaises(TypeError):
            class C(type(NotRequired[int])):
                pass

    def test_cannot_init(self):
        with self.assertRaises(TypeError):
            NotRequired()
        with self.assertRaises(TypeError):
            type(NotRequired)()
        with self.assertRaises(TypeError):
            type(NotRequired[Optional[int]])()

    def test_no_isinstance(self):
        with self.assertRaises(TypeError):
            isinstance(1, NotRequired[int])
        with self.assertRaises(TypeError):
            issubclass(int, NotRequired)


class IntVarTests(BaseTestCase):
    def test_valid(self):
        T_ints = IntVar("T_ints")

    def test_invalid(self):
        with self.assertRaises(TypeError):
            T_ints = IntVar("T_ints", int)
        with self.assertRaises(TypeError):
            T_ints = IntVar("T_ints", bound=int)
        with self.assertRaises(TypeError):
            T_ints = IntVar("T_ints", covariant=True)


class LiteralTests(BaseTestCase):
    def test_basics(self):
        Literal[1]
        Literal[1, 2, 3]
        Literal["x", "y", "z"]
        Literal[None]

    def test_enum(self):
        import enum
        class My(enum.Enum):
            A = 'A'

        self.assertEqual(Literal[My.A].__args__, (My.A,))

    def test_illegal_parameters_do_not_raise_runtime_errors(self):
        # Type checkers should reject these types, but we do not
        # raise errors at runtime to maintain maximum flexibility
        Literal[int]
        Literal[Literal[1, 2], Literal[4, 5]]
        Literal[3j + 2, ..., ()]
        Literal[b"foo", u"bar"]
        Literal[{"foo": 3, "bar": 4}]
        Literal[T]

    def test_literals_inside_other_types(self):
        List[Literal[1, 2, 3]]
        List[Literal[("foo", "bar", "baz")]]

    def test_repr(self):
        # we backport various bugfixes that were added in 3.10.1 and earlier
        if sys.version_info >= (3, 10, 1):
            mod_name = 'typing'
        else:
            mod_name = 'typing_extensions'
        self.assertEqual(repr(Literal[1]), mod_name + ".Literal[1]")
        self.assertEqual(repr(Literal[1, True, "foo"]), mod_name + ".Literal[1, True, 'foo']")
        self.assertEqual(repr(Literal[int]), mod_name + ".Literal[int]")
        self.assertEqual(repr(Literal), mod_name + ".Literal")
        self.assertEqual(repr(Literal[None]), mod_name + ".Literal[None]")
        self.assertEqual(repr(Literal[1, 2, 3, 3]), mod_name + ".Literal[1, 2, 3]")

    def test_cannot_init(self):
        with self.assertRaises(TypeError):
            Literal()
        with self.assertRaises(TypeError):
            Literal[1]()
        with self.assertRaises(TypeError):
            type(Literal)()
        with self.assertRaises(TypeError):
            type(Literal[1])()

    def test_no_isinstance_or_issubclass(self):
        with self.assertRaises(TypeError):
            isinstance(1, Literal[1])
        with self.assertRaises(TypeError):
            isinstance(int, Literal[1])
        with self.assertRaises(TypeError):
            issubclass(1, Literal[1])
        with self.assertRaises(TypeError):
            issubclass(int, Literal[1])

    def test_no_subclassing(self):
        with self.assertRaises(TypeError):
            class Foo(Literal[1]): pass
        with self.assertRaises(TypeError):
            class Bar(Literal): pass

    def test_no_multiple_subscripts(self):
        with self.assertRaises(TypeError):
            Literal[1][1]

    def test_equal(self):
        self.assertNotEqual(Literal[0], Literal[False])
        self.assertNotEqual(Literal[True], Literal[1])
        self.assertNotEqual(Literal[1], Literal[2])
        self.assertNotEqual(Literal[1, True], Literal[1])
        self.assertNotEqual(Literal[1, True], Literal[1, 1])
        self.assertNotEqual(Literal[1, 2], Literal[True, 2])
        self.assertEqual(Literal[1], Literal[1])
        self.assertEqual(Literal[1, 2], Literal[2, 1])
        self.assertEqual(Literal[1, 2, 3], Literal[1, 2, 3, 3])

    def test_hash(self):
        self.assertEqual(hash(Literal[1]), hash(Literal[1]))
        self.assertEqual(hash(Literal[1, 2]), hash(Literal[2, 1]))
        self.assertEqual(hash(Literal[1, 2, 3]), hash(Literal[1, 2, 3, 3]))

    def test_args(self):
        self.assertEqual(Literal[1, 2, 3].__args__, (1, 2, 3))
        self.assertEqual(Literal[1, 2, 3, 3].__args__, (1, 2, 3))
        self.assertEqual(Literal[1, Literal[2], Literal[3, 4]].__args__, (1, 2, 3, 4))
        # Mutable arguments will not be deduplicated
        self.assertEqual(Literal[[], []].__args__, ([], []))

    def test_union_of_literals(self):
        self.assertEqual(Union[Literal[1], Literal[2]].__args__,
                         (Literal[1], Literal[2]))
        self.assertEqual(Union[Literal[1], Literal[1]],
                         Literal[1])

        self.assertEqual(Union[Literal[False], Literal[0]].__args__,
                         (Literal[False], Literal[0]))
        self.assertEqual(Union[Literal[True], Literal[1]].__args__,
                         (Literal[True], Literal[1]))

        import enum
        class Ints(enum.IntEnum):
            A = 0
            B = 1

        self.assertEqual(Union[Literal[Ints.A], Literal[Ints.B]].__args__,
                         (Literal[Ints.A], Literal[Ints.B]))

        self.assertEqual(Union[Literal[Ints.A], Literal[Ints.A]],
                         Literal[Ints.A])
        self.assertEqual(Union[Literal[Ints.B], Literal[Ints.B]],
                         Literal[Ints.B])

        self.assertEqual(Union[Literal[0], Literal[Ints.A], Literal[False]].__args__,
                         (Literal[0], Literal[Ints.A], Literal[False]))
        self.assertEqual(Union[Literal[1], Literal[Ints.B], Literal[True]].__args__,
                         (Literal[1], Literal[Ints.B], Literal[True]))

    @skipUnless(TYPING_3_10_0, "Python 3.10+ required")
    def test_or_type_operator_with_Literal(self):
        self.assertEqual((Literal[1] | Literal[2]).__args__,
                         (Literal[1], Literal[2]))

        self.assertEqual((Literal[0] | Literal[False]).__args__,
                         (Literal[0], Literal[False]))
        self.assertEqual((Literal[1] | Literal[True]).__args__,
                         (Literal[1], Literal[True]))

        self.assertEqual(Literal[1] | Literal[1], Literal[1])
        self.assertEqual(Literal['a'] | Literal['a'], Literal['a'])

        import enum
        class Ints(enum.IntEnum):
            A = 0
            B = 1

        self.assertEqual(Literal[Ints.A] | Literal[Ints.A], Literal[Ints.A])
        self.assertEqual(Literal[Ints.B] | Literal[Ints.B], Literal[Ints.B])

        self.assertEqual((Literal[Ints.B] | Literal[Ints.A]).__args__,
                         (Literal[Ints.B], Literal[Ints.A]))

        self.assertEqual((Literal[0] | Literal[Ints.A]).__args__,
                         (Literal[0], Literal[Ints.A]))
        self.assertEqual((Literal[1] | Literal[Ints.B]).__args__,
                         (Literal[1], Literal[Ints.B]))

    def test_flatten(self):
        l1 = Literal[Literal[1], Literal[2], Literal[3]]
        l2 = Literal[Literal[1, 2], 3]
        l3 = Literal[Literal[1, 2, 3]]
        for lit in l1, l2, l3:
            self.assertEqual(lit, Literal[1, 2, 3])
            self.assertEqual(lit.__args__, (1, 2, 3))

    def test_does_not_flatten_enum(self):
        import enum
        class Ints(enum.IntEnum):
            A = 1
            B = 2

        literal = Literal[
            Literal[Ints.A],
            Literal[Ints.B],
            Literal[1],
            Literal[2],
        ]
        self.assertEqual(literal.__args__, (Ints.A, Ints.B, 1, 2))

    def test_caching_of_Literal_respects_type(self):
        self.assertIs(type(Literal[1].__args__[0]), int)
        self.assertIs(type(Literal[True].__args__[0]), bool)


class MethodHolder:
    @classmethod
    def clsmethod(cls): ...
    @staticmethod
    def stmethod(): ...
    def method(self): ...


if TYPING_3_11_0:
    registry_holder = typing
else:
    registry_holder = typing_extensions


class OverloadTests(BaseTestCase):

    def test_overload_fails(self):
        with self.assertRaises(RuntimeError):

            @overload
            def blah():
                pass

            blah()

    def test_overload_succeeds(self):
        @overload
        def blah():
            pass

        def blah():
            pass

        blah()

    @skipIf(
        sys.implementation.name == "pypy",
        "sum() and print() are not compiled in pypy"
    )
    @patch(
        f"{registry_holder.__name__}._overload_registry",
        defaultdict(lambda: defaultdict(dict))
    )
    def test_overload_on_compiled_functions(self):
        registry = registry_holder._overload_registry
        # The registry starts out empty:
        self.assertEqual(registry, {})

        # This should just not fail:
        overload(sum)
        overload(print)

        # No overloads are recorded:
        self.assertEqual(get_overloads(sum), [])
        self.assertEqual(get_overloads(print), [])

    def set_up_overloads(self):
        def blah():
            pass

        overload1 = blah
        overload(blah)

        def blah():
            pass

        overload2 = blah
        overload(blah)

        def blah():
            pass

        return blah, [overload1, overload2]

    # Make sure we don't clear the global overload registry
    @patch(
        f"{registry_holder.__name__}._overload_registry",
        defaultdict(lambda: defaultdict(dict))
    )
    def test_overload_registry(self):
        registry = registry_holder._overload_registry
        # The registry starts out empty
        self.assertEqual(registry, {})

        impl, overloads = self.set_up_overloads()
        self.assertNotEqual(registry, {})
        self.assertEqual(list(get_overloads(impl)), overloads)

        def some_other_func(): pass
        overload(some_other_func)
        other_overload = some_other_func
        def some_other_func(): pass
        self.assertEqual(list(get_overloads(some_other_func)), [other_overload])
        # Unrelated function still has no overloads:
        def not_overloaded(): pass
        self.assertEqual(list(get_overloads(not_overloaded)), [])

        # Make sure that after we clear all overloads, the registry is
        # completely empty.
        clear_overloads()
        self.assertEqual(registry, {})
        self.assertEqual(get_overloads(impl), [])

        # Querying a function with no overloads shouldn't change the registry.
        def the_only_one(): pass
        self.assertEqual(get_overloads(the_only_one), [])
        self.assertEqual(registry, {})

    def test_overload_registry_repeated(self):
        for _ in range(2):
            impl, overloads = self.set_up_overloads()

            self.assertEqual(list(get_overloads(impl)), overloads)


class AssertTypeTests(BaseTestCase):

    def test_basics(self):
        arg = 42
        self.assertIs(assert_type(arg, int), arg)
        self.assertIs(assert_type(arg, Union[str, float]), arg)
        self.assertIs(assert_type(arg, AnyStr), arg)
        self.assertIs(assert_type(arg, None), arg)

    def test_errors(self):
        # Bogus calls are not expected to fail.
        arg = 42
        self.assertIs(assert_type(arg, 42), arg)
        self.assertIs(assert_type(arg, 'hello'), arg)


T_a = TypeVar('T_a')

class AwaitableWrapper(Awaitable[T_a]):

    def __init__(self, value):
        self.value = value

    def __await__(self) -> typing.Iterator[T_a]:
        yield
        return self.value

class AsyncIteratorWrapper(AsyncIterator[T_a]):

    def __init__(self, value: Iterable[T_a]):
        self.value = value

    def __aiter__(self) -> AsyncIterator[T_a]:
        return self

    async def __anext__(self) -> T_a:
        data = await self.value
        if data:
            return data
        else:
            raise StopAsyncIteration

class ACM:
    async def __aenter__(self) -> int:
        return 42

    async def __aexit__(self, etype, eval, tb):
        return None



class A:
    y: float
class B(A):
    x: ClassVar[Optional['B']] = None
    y: int
    b: int
class CSub(B):
    z: ClassVar['CSub'] = B()
class G(Generic[T]):
    lst: ClassVar[List[T]] = []

class Loop:
    attr: Final['Loop']

class NoneAndForward:
    parent: 'NoneAndForward'
    meaning: None

class XRepr(NamedTuple):
    x: int
    y: int = 1

    def __str__(self):
        return f'{self.x} -> {self.y}'

    def __add__(self, other):
        return 0

@runtime_checkable
class HasCallProtocol(Protocol):
    __call__: typing.Callable


async def g_with(am: AsyncContextManager[int]):
    x: int
    async with am as x:
        return x

try:
    g_with(ACM()).send(None)
except StopIteration as e:
    assert e.args[0] == 42

Label = TypedDict('Label', [('label', str)])

class Point2D(TypedDict):
    x: int
    y: int

class Point2Dor3D(Point2D, total=False):
    z: int

class LabelPoint2D(Point2D, Label): ...

class Options(TypedDict, total=False):
    log_level: int
    log_path: str

class BaseAnimal(TypedDict):
    name: str

class Animal(BaseAnimal, total=False):
    voice: str
    tail: bool

class Cat(Animal):
    fur_color: str

class TotalMovie(TypedDict):
    title: str
    year: NotRequired[int]

class NontotalMovie(TypedDict, total=False):
    title: Required[str]
    year: int

class AnnotatedMovie(TypedDict):
    title: Annotated[Required[str], "foobar"]
    year: NotRequired[Annotated[int, 2000]]


gth = get_type_hints


class GetTypeHintTests(BaseTestCase):
    @classmethod
    def setUpClass(cls):
        with tempfile.TemporaryDirectory() as tempdir:
            sys.path.append(tempdir)
            Path(tempdir, "ann_module.py").write_text(ANN_MODULE_SOURCE)
            Path(tempdir, "ann_module2.py").write_text(ANN_MODULE_2_SOURCE)
            Path(tempdir, "ann_module3.py").write_text(ANN_MODULE_3_SOURCE)
            cls.ann_module = importlib.import_module("ann_module")
            cls.ann_module2 = importlib.import_module("ann_module2")
            cls.ann_module3 = importlib.import_module("ann_module3")
        sys.path.pop()

    @classmethod
    def tearDownClass(cls):
        for modname in "ann_module", "ann_module2", "ann_module3":
            delattr(cls, modname)
            del sys.modules[modname]

    def test_get_type_hints_modules(self):
        ann_module_type_hints = {1: 2, 'f': Tuple[int, int], 'x': int, 'y': str}
        self.assertEqual(gth(self.ann_module), ann_module_type_hints)
        self.assertEqual(gth(self.ann_module2), {})
        self.assertEqual(gth(self.ann_module3), {})

    def test_get_type_hints_classes(self):
        self.assertEqual(gth(self.ann_module.C, self.ann_module.__dict__),
                         {'y': Optional[self.ann_module.C]})
        self.assertIsInstance(gth(self.ann_module.j_class), dict)
        self.assertEqual(gth(self.ann_module.M), {'123': 123, 'o': type})
        self.assertEqual(gth(self.ann_module.D),
                         {'j': str, 'k': str, 'y': Optional[self.ann_module.C]})
        self.assertEqual(gth(self.ann_module.Y), {'z': int})
        self.assertEqual(gth(self.ann_module.h_class),
                         {'y': Optional[self.ann_module.C]})
        self.assertEqual(gth(self.ann_module.S), {'x': str, 'y': str})
        self.assertEqual(gth(self.ann_module.foo), {'x': int})
        self.assertEqual(gth(NoneAndForward, globals()),
                         {'parent': NoneAndForward, 'meaning': type(None)})

    def test_respect_no_type_check(self):
        @no_type_check
        class NoTpCheck:
            class Inn:
                def __init__(self, x: 'not a type'): ...
        self.assertTrue(NoTpCheck.__no_type_check__)
        self.assertTrue(NoTpCheck.Inn.__init__.__no_type_check__)
        self.assertEqual(gth(self.ann_module2.NTC.meth), {})
        class ABase(Generic[T]):
            def meth(x: int): ...
        @no_type_check
        class Der(ABase): ...
        self.assertEqual(gth(ABase.meth), {'x': int})

    def test_get_type_hints_ClassVar(self):
        self.assertEqual(gth(self.ann_module2.CV, self.ann_module2.__dict__),
                         {'var': ClassVar[self.ann_module2.CV]})
        self.assertEqual(gth(B, globals()),
                         {'y': int, 'x': ClassVar[Optional[B]], 'b': int})
        self.assertEqual(gth(CSub, globals()),
                         {'z': ClassVar[CSub], 'y': int, 'b': int,
                          'x': ClassVar[Optional[B]]})
        self.assertEqual(gth(G), {'lst': ClassVar[List[T]]})

    def test_final_forward_ref(self):
        self.assertEqual(gth(Loop, globals())['attr'], Final[Loop])
        self.assertNotEqual(gth(Loop, globals())['attr'], Final[int])
        self.assertNotEqual(gth(Loop, globals())['attr'], Final)


class GetUtilitiesTestCase(TestCase):
    def test_get_origin(self):
        T = TypeVar('T')
        P = ParamSpec('P')
        Ts = TypeVarTuple('Ts')
        class C(Generic[T]): pass
        self.assertIs(get_origin(C[int]), C)
        self.assertIs(get_origin(C[T]), C)
        self.assertIs(get_origin(int), None)
        self.assertIs(get_origin(ClassVar[int]), ClassVar)
        self.assertIs(get_origin(Union[int, str]), Union)
        self.assertIs(get_origin(Literal[42, 43]), Literal)
        self.assertIs(get_origin(Final[List[int]]), Final)
        self.assertIs(get_origin(Generic), Generic)
        self.assertIs(get_origin(Generic[T]), Generic)
        self.assertIs(get_origin(List[Tuple[T, T]][int]), list)
        self.assertIs(get_origin(Annotated[T, 'thing']), Annotated)
        self.assertIs(get_origin(List), list)
        self.assertIs(get_origin(Tuple), tuple)
        self.assertIs(get_origin(Callable), collections.abc.Callable)
        if sys.version_info >= (3, 9):
            self.assertIs(get_origin(list[int]), list)
        self.assertIs(get_origin(list), None)
        self.assertIs(get_origin(P.args), P)
        self.assertIs(get_origin(P.kwargs), P)
        self.assertIs(get_origin(Required[int]), Required)
        self.assertIs(get_origin(NotRequired[int]), NotRequired)
        self.assertIs(get_origin(Unpack[Ts]), Unpack)
        self.assertIs(get_origin(Unpack), None)

    def test_get_args(self):
        T = TypeVar('T')
        Ts = TypeVarTuple('Ts')
        class C(Generic[T]): pass
        self.assertEqual(get_args(C[int]), (int,))
        self.assertEqual(get_args(C[T]), (T,))
        self.assertEqual(get_args(int), ())
        self.assertEqual(get_args(ClassVar[int]), (int,))
        self.assertEqual(get_args(Union[int, str]), (int, str))
        self.assertEqual(get_args(Literal[42, 43]), (42, 43))
        self.assertEqual(get_args(Final[List[int]]), (List[int],))
        self.assertEqual(get_args(Union[int, Tuple[T, int]][str]),
                         (int, Tuple[str, int]))
        self.assertEqual(get_args(typing.Dict[int, Tuple[T, T]][Optional[int]]),
                         (int, Tuple[Optional[int], Optional[int]]))
        self.assertEqual(get_args(Callable[[], T][int]), ([], int))
        self.assertEqual(get_args(Callable[..., int]), (..., int))
        self.assertEqual(get_args(Union[int, Callable[[Tuple[T, ...]], str]]),
                         (int, Callable[[Tuple[T, ...]], str]))
        self.assertEqual(get_args(Tuple[int, ...]), (int, ...))
        if TYPING_3_11_0:
            self.assertEqual(get_args(Tuple[()]), ())
        else:
            self.assertEqual(get_args(Tuple[()]), ((),))
        self.assertEqual(get_args(Annotated[T, 'one', 2, ['three']]), (T, 'one', 2, ['three']))
        self.assertEqual(get_args(List), ())
        self.assertEqual(get_args(Tuple), ())
        self.assertEqual(get_args(Callable), ())
        if sys.version_info >= (3, 9):
            self.assertEqual(get_args(list[int]), (int,))
        self.assertEqual(get_args(list), ())
        if sys.version_info >= (3, 9):
            # Support Python versions with and without the fix for
            # https://bugs.python.org/issue42195
            # The first variant is for 3.9.2+, the second for 3.9.0 and 1
            self.assertIn(get_args(collections.abc.Callable[[int], str]),
                          (([int], str), ([[int]], str)))
            self.assertIn(get_args(collections.abc.Callable[[], str]),
                          (([], str), ([[]], str)))
            self.assertEqual(get_args(collections.abc.Callable[..., str]), (..., str))
        P = ParamSpec('P')
        # In 3.9 and lower we use typing_extensions's hacky implementation
        # of ParamSpec, which gets incorrectly wrapped in a list
        self.assertIn(get_args(Callable[P, int]), [(P, int), ([P], int)])
        self.assertEqual(get_args(Callable[Concatenate[int, P], int]),
                         (Concatenate[int, P], int))
        self.assertEqual(get_args(Required[int]), (int,))
        self.assertEqual(get_args(NotRequired[int]), (int,))
        self.assertEqual(get_args(Unpack[Ts]), (Ts,))
        self.assertEqual(get_args(Unpack), ())


class CollectionsAbcTests(BaseTestCase):

    def test_isinstance_collections(self):
        self.assertNotIsInstance(1, collections.abc.Mapping)
        self.assertNotIsInstance(1, collections.abc.Iterable)
        self.assertNotIsInstance(1, collections.abc.Container)
        self.assertNotIsInstance(1, collections.abc.Sized)
        with self.assertRaises(TypeError):
            isinstance(collections.deque(), typing_extensions.Deque[int])
        with self.assertRaises(TypeError):
            issubclass(collections.Counter, typing_extensions.Counter[str])

    def test_awaitable(self):
        ns = {}
        exec(
            "async def foo() -> typing_extensions.Awaitable[int]:\n"
            "    return await AwaitableWrapper(42)\n",
            globals(), ns)
        foo = ns['foo']
        g = foo()
        self.assertIsInstance(g, typing_extensions.Awaitable)
        self.assertNotIsInstance(foo, typing_extensions.Awaitable)
        g.send(None)  # Run foo() till completion, to avoid warning.

    def test_coroutine(self):
        ns = {}
        exec(
            "async def foo():\n"
            "    return\n",
            globals(), ns)
        foo = ns['foo']
        g = foo()
        self.assertIsInstance(g, typing_extensions.Coroutine)
        with self.assertRaises(TypeError):
            isinstance(g, typing_extensions.Coroutine[int])
        self.assertNotIsInstance(foo, typing_extensions.Coroutine)
        try:
            g.send(None)
        except StopIteration:
            pass

    def test_async_iterable(self):
        base_it: Iterator[int] = range(10)
        it = AsyncIteratorWrapper(base_it)
        self.assertIsInstance(it, typing_extensions.AsyncIterable)
        self.assertIsInstance(it, typing_extensions.AsyncIterable)
        self.assertNotIsInstance(42, typing_extensions.AsyncIterable)

    def test_async_iterator(self):
        base_it: Iterator[int] = range(10)
        it = AsyncIteratorWrapper(base_it)
        self.assertIsInstance(it, typing_extensions.AsyncIterator)
        self.assertNotIsInstance(42, typing_extensions.AsyncIterator)

    def test_deque(self):
        self.assertIsSubclass(collections.deque, typing_extensions.Deque)
        class MyDeque(typing_extensions.Deque[int]): ...
        self.assertIsInstance(MyDeque(), collections.deque)

    def test_counter(self):
        self.assertIsSubclass(collections.Counter, typing_extensions.Counter)

    def test_defaultdict_instantiation(self):
        self.assertIs(
            type(typing_extensions.DefaultDict()),
            collections.defaultdict)
        self.assertIs(
            type(typing_extensions.DefaultDict[KT, VT]()),
            collections.defaultdict)
        self.assertIs(
            type(typing_extensions.DefaultDict[str, int]()),
            collections.defaultdict)

    def test_defaultdict_subclass(self):

        class MyDefDict(typing_extensions.DefaultDict[str, int]):
            pass

        dd = MyDefDict()
        self.assertIsInstance(dd, MyDefDict)

        self.assertIsSubclass(MyDefDict, collections.defaultdict)
        self.assertNotIsSubclass(collections.defaultdict, MyDefDict)

    def test_ordereddict_instantiation(self):
        self.assertIs(
            type(typing_extensions.OrderedDict()),
            collections.OrderedDict)
        self.assertIs(
            type(typing_extensions.OrderedDict[KT, VT]()),
            collections.OrderedDict)
        self.assertIs(
            type(typing_extensions.OrderedDict[str, int]()),
            collections.OrderedDict)

    def test_ordereddict_subclass(self):

        class MyOrdDict(typing_extensions.OrderedDict[str, int]):
            pass

        od = MyOrdDict()
        self.assertIsInstance(od, MyOrdDict)

        self.assertIsSubclass(MyOrdDict, collections.OrderedDict)
        self.assertNotIsSubclass(collections.OrderedDict, MyOrdDict)

    def test_chainmap_instantiation(self):
        self.assertIs(type(typing_extensions.ChainMap()), collections.ChainMap)
        self.assertIs(type(typing_extensions.ChainMap[KT, VT]()), collections.ChainMap)
        self.assertIs(type(typing_extensions.ChainMap[str, int]()), collections.ChainMap)
        class CM(typing_extensions.ChainMap[KT, VT]): ...
        self.assertIs(type(CM[int, str]()), CM)

    def test_chainmap_subclass(self):

        class MyChainMap(typing_extensions.ChainMap[str, int]):
            pass

        cm = MyChainMap()
        self.assertIsInstance(cm, MyChainMap)

        self.assertIsSubclass(MyChainMap, collections.ChainMap)
        self.assertNotIsSubclass(collections.ChainMap, MyChainMap)

    def test_deque_instantiation(self):
        self.assertIs(type(typing_extensions.Deque()), collections.deque)
        self.assertIs(type(typing_extensions.Deque[T]()), collections.deque)
        self.assertIs(type(typing_extensions.Deque[int]()), collections.deque)
        class D(typing_extensions.Deque[T]): ...
        self.assertIs(type(D[int]()), D)

    def test_counter_instantiation(self):
        self.assertIs(type(typing_extensions.Counter()), collections.Counter)
        self.assertIs(type(typing_extensions.Counter[T]()), collections.Counter)
        self.assertIs(type(typing_extensions.Counter[int]()), collections.Counter)
        class C(typing_extensions.Counter[T]): ...
        self.assertIs(type(C[int]()), C)
        self.assertEqual(C.__bases__, (collections.Counter, typing.Generic))

    def test_counter_subclass_instantiation(self):

        class MyCounter(typing_extensions.Counter[int]):
            pass

        d = MyCounter()
        self.assertIsInstance(d, MyCounter)
        self.assertIsInstance(d, collections.Counter)
        self.assertIsInstance(d, typing_extensions.Counter)

    def test_async_generator(self):
        ns = {}
        exec("async def f():\n"
             "    yield 42\n", globals(), ns)
        g = ns['f']()
        self.assertIsSubclass(type(g), typing_extensions.AsyncGenerator)

    def test_no_async_generator_instantiation(self):
        with self.assertRaises(TypeError):
            typing_extensions.AsyncGenerator()
        with self.assertRaises(TypeError):
            typing_extensions.AsyncGenerator[T, T]()
        with self.assertRaises(TypeError):
            typing_extensions.AsyncGenerator[int, int]()

    def test_subclassing_async_generator(self):
        class G(typing_extensions.AsyncGenerator[int, int]):
            def asend(self, value):
                pass
            def athrow(self, typ, val=None, tb=None):
                pass

        ns = {}
        exec('async def g(): yield 0', globals(), ns)
        g = ns['g']
        self.assertIsSubclass(G, typing_extensions.AsyncGenerator)
        self.assertIsSubclass(G, typing_extensions.AsyncIterable)
        self.assertIsSubclass(G, collections.abc.AsyncGenerator)
        self.assertIsSubclass(G, collections.abc.AsyncIterable)
        self.assertNotIsSubclass(type(g), G)

        instance = G()
        self.assertIsInstance(instance, typing_extensions.AsyncGenerator)
        self.assertIsInstance(instance, typing_extensions.AsyncIterable)
        self.assertIsInstance(instance, collections.abc.AsyncGenerator)
        self.assertIsInstance(instance, collections.abc.AsyncIterable)
        self.assertNotIsInstance(type(g), G)
        self.assertNotIsInstance(g, G)


class OtherABCTests(BaseTestCase):

    def test_contextmanager(self):
        @contextlib.contextmanager
        def manager():
            yield 42

        cm = manager()
        self.assertIsInstance(cm, typing_extensions.ContextManager)
        self.assertNotIsInstance(42, typing_extensions.ContextManager)

    def test_async_contextmanager(self):
        class NotACM:
            pass
        self.assertIsInstance(ACM(), typing_extensions.AsyncContextManager)
        self.assertNotIsInstance(NotACM(), typing_extensions.AsyncContextManager)
        @contextlib.contextmanager
        def manager():
            yield 42

        cm = manager()
        self.assertNotIsInstance(cm, typing_extensions.AsyncContextManager)
        self.assertEqual(typing_extensions.AsyncContextManager[int].__args__, (int,))
        with self.assertRaises(TypeError):
            isinstance(42, typing_extensions.AsyncContextManager[int])
        with self.assertRaises(TypeError):
            typing_extensions.AsyncContextManager[int, str]


class TypeTests(BaseTestCase):

    def test_type_basic(self):

        class User: pass
        class BasicUser(User): pass
        class ProUser(User): pass

        def new_user(user_class: Type[User]) -> User:
            return user_class()

        new_user(BasicUser)

    def test_type_typevar(self):

        class User: pass
        class BasicUser(User): pass
        class ProUser(User): pass

        U = TypeVar('U', bound=User)

        def new_user(user_class: Type[U]) -> U:
            return user_class()

        new_user(BasicUser)

    def test_type_optional(self):
        A = Optional[Type[BaseException]]

        def foo(a: A) -> Optional[BaseException]:
            if a is None:
                return None
            else:
                return a()

        assert isinstance(foo(KeyboardInterrupt), KeyboardInterrupt)
        assert foo(None) is None


class NewTypeTests(BaseTestCase):
    @classmethod
    def setUpClass(cls):
        global UserId
        UserId = NewType('UserId', int)
        cls.UserName = NewType(cls.__qualname__ + '.UserName', str)

    @classmethod
    def tearDownClass(cls):
        global UserId
        del UserId
        del cls.UserName

    def test_basic(self):
        self.assertIsInstance(UserId(5), int)
        self.assertIsInstance(self.UserName('Joe'), str)
        self.assertEqual(UserId(5) + 1, 6)

    def test_errors(self):
        with self.assertRaises(TypeError):
            issubclass(UserId, int)
        with self.assertRaises(TypeError):
            class D(UserId):
                pass

    @skipUnless(TYPING_3_10_0, "PEP 604 has yet to be")
    def test_or(self):
        for cls in (int, self.UserName):
            with self.subTest(cls=cls):
                self.assertEqual(UserId | cls, Union[UserId, cls])
                self.assertEqual(cls | UserId, Union[cls, UserId])

                self.assertEqual(get_args(UserId | cls), (UserId, cls))
                self.assertEqual(get_args(cls | UserId), (cls, UserId))

    def test_special_attrs(self):
        self.assertEqual(UserId.__name__, 'UserId')
        self.assertEqual(UserId.__qualname__, 'UserId')
        self.assertEqual(UserId.__module__, __name__)
        self.assertEqual(UserId.__supertype__, int)

        UserName = self.UserName
        self.assertEqual(UserName.__name__, 'UserName')
        self.assertEqual(UserName.__qualname__,
                         self.__class__.__qualname__ + '.UserName')
        self.assertEqual(UserName.__module__, __name__)
        self.assertEqual(UserName.__supertype__, str)

    def test_repr(self):
        self.assertEqual(repr(UserId), f'{__name__}.UserId')
        self.assertEqual(repr(self.UserName),
                         f'{__name__}.{self.__class__.__qualname__}.UserName')

    def test_pickle(self):
        UserAge = NewType('UserAge', float)
        for proto in range(pickle.HIGHEST_PROTOCOL + 1):
            with self.subTest(proto=proto):
                pickled = pickle.dumps(UserId, proto)
                loaded = pickle.loads(pickled)
                self.assertIs(loaded, UserId)

                pickled = pickle.dumps(self.UserName, proto)
                loaded = pickle.loads(pickled)
                self.assertIs(loaded, self.UserName)

                with self.assertRaises(pickle.PicklingError):
                    pickle.dumps(UserAge, proto)

    def test_missing__name__(self):
        code = ("import typing_extensions\n"
                "NT = typing_extensions.NewType('NT', int)\n"
                )
        exec(code, {})

    def test_error_message_when_subclassing(self):
        with self.assertRaisesRegex(
            TypeError,
            re.escape(
                "Cannot subclass an instance of NewType. Perhaps you were looking for: "
                "`ProUserId = NewType('ProUserId', UserId)`"
            )
        ):
            class ProUserId(UserId):
                ...


class Coordinate(Protocol):
    x: int
    y: int

@runtime_checkable
class Point(Coordinate, Protocol):
    label: str

class MyPoint:
    x: int
    y: int
    label: str

class XAxis(Protocol):
    x: int

class YAxis(Protocol):
    y: int

@runtime_checkable
class Position(XAxis, YAxis, Protocol):
    pass

@runtime_checkable
class Proto(Protocol):
    attr: int

    def meth(self, arg: str) -> int:
        ...

class Concrete(Proto):
    pass

class Other:
    attr: int = 1

    def meth(self, arg: str) -> int:
        if arg == 'this':
            return 1
        return 0

class NT(NamedTuple):
    x: int
    y: int


skip_if_py312b1 = skipIf(
    sys.version_info == (3, 12, 0, 'beta', 1),
    "CPython had bugs in 3.12.0b1"
)


class ProtocolTests(BaseTestCase):
    def test_runtime_alias(self):
        self.assertIs(runtime, runtime_checkable)

    def test_basic_protocol(self):
        @runtime_checkable
        class P(Protocol):
            def meth(self):
                pass
        class C: pass
        class D:
            def meth(self):
                pass
        def f():
            pass
        self.assertIsSubclass(D, P)
        self.assertIsInstance(D(), P)
        self.assertNotIsSubclass(C, P)
        self.assertNotIsInstance(C(), P)
        self.assertNotIsSubclass(types.FunctionType, P)
        self.assertNotIsInstance(f, P)

    def test_everything_implements_empty_protocol(self):
        @runtime_checkable
        class Empty(Protocol): pass
        class C: pass
        def f():
            pass
        for thing in (object, type, tuple, C, types.FunctionType):
            self.assertIsSubclass(thing, Empty)
        for thing in (object(), 1, (), typing, f):
            self.assertIsInstance(thing, Empty)

    def test_function_implements_protocol(self):
        def f():
            pass
        self.assertIsInstance(f, HasCallProtocol)

    def test_no_inheritance_from_nominal(self):
        class C: pass
        class BP(Protocol): pass
        with self.assertRaises(TypeError):
            class P(C, Protocol):
                pass
        with self.assertRaises(TypeError):
            class P(Protocol, C):
                pass
        with self.assertRaises(TypeError):
            class P(BP, C, Protocol):
                pass
        class D(BP, C): pass
        class E(C, BP): pass
        self.assertNotIsInstance(D(), E)
        self.assertNotIsInstance(E(), D)

    @skipUnless(
        hasattr(typing, "Protocol"),
        "Test is only relevant if typing.Protocol exists"
    )
    def test_runtimecheckable_on_typing_dot_Protocol(self):
        @runtime_checkable
        class Foo(typing.Protocol):
            x: int

        class Bar:
            def __init__(self):
                self.x = 42

        self.assertIsInstance(Bar(), Foo)
        self.assertNotIsInstance(object(), Foo)

    def test_no_instantiation(self):
        class P(Protocol): pass
        with self.assertRaises(TypeError):
            P()
        class C(P): pass
        self.assertIsInstance(C(), C)
        T = TypeVar('T')
        class PG(Protocol[T]): pass
        with self.assertRaises(TypeError):
            PG()
        with self.assertRaises(TypeError):
            PG[int]()
        with self.assertRaises(TypeError):
            PG[T]()
        class CG(PG[T]): pass
        self.assertIsInstance(CG[int](), CG)

    def test_protocol_defining_init_does_not_get_overridden(self):
        # check that P.__init__ doesn't get clobbered
        # see https://bugs.python.org/issue44807

        class P(Protocol):
            x: int
            def __init__(self, x: int) -> None:
                self.x = x
        class C: pass

        c = C()
        P.__init__(c, 1)
        self.assertEqual(c.x, 1)

    def test_concrete_class_inheriting_init_from_protocol(self):
        class P(Protocol):
            x: int
            def __init__(self, x: int) -> None:
                self.x = x

        class C(P): pass

        c = C(1)
        self.assertIsInstance(c, C)
        self.assertEqual(c.x, 1)

    def test_cannot_instantiate_abstract(self):
        @runtime_checkable
        class P(Protocol):
            @abc.abstractmethod
            def ameth(self) -> int:
                raise NotImplementedError
        class B(P):
            pass
        class C(B):
            def ameth(self) -> int:
                return 26
        with self.assertRaises(TypeError):
            B()
        self.assertIsInstance(C(), P)

    def test_subprotocols_extending(self):
        class P1(Protocol):
            def meth1(self):
                pass
        @runtime_checkable
        class P2(P1, Protocol):
            def meth2(self):
                pass
        class C:
            def meth1(self):
                pass
            def meth2(self):
                pass
        class C1:
            def meth1(self):
                pass
        class C2:
            def meth2(self):
                pass
        self.assertNotIsInstance(C1(), P2)
        self.assertNotIsInstance(C2(), P2)
        self.assertNotIsSubclass(C1, P2)
        self.assertNotIsSubclass(C2, P2)
        self.assertIsInstance(C(), P2)
        self.assertIsSubclass(C, P2)

    def test_subprotocols_merging(self):
        class P1(Protocol):
            def meth1(self):
                pass
        class P2(Protocol):
            def meth2(self):
                pass
        @runtime_checkable
        class P(P1, P2, Protocol):
            pass
        class C:
            def meth1(self):
                pass
            def meth2(self):
                pass
        class C1:
            def meth1(self):
                pass
        class C2:
            def meth2(self):
                pass
        self.assertNotIsInstance(C1(), P)
        self.assertNotIsInstance(C2(), P)
        self.assertNotIsSubclass(C1, P)
        self.assertNotIsSubclass(C2, P)
        self.assertIsInstance(C(), P)
        self.assertIsSubclass(C, P)

    def test_protocols_issubclass(self):
        T = TypeVar('T')
        @runtime_checkable
        class P(Protocol):
            def x(self): ...
        @runtime_checkable
        class PG(Protocol[T]):
            def x(self): ...
        class BadP(Protocol):
            def x(self): ...
        class BadPG(Protocol[T]):
            def x(self): ...
        class C:
            def x(self): ...
        self.assertIsSubclass(C, P)
        self.assertIsSubclass(C, PG)
        self.assertIsSubclass(BadP, PG)

        no_subscripted_generics = (
            "Subscripted generics cannot be used with class and instance checks"
        )

        with self.assertRaisesRegex(TypeError, no_subscripted_generics):
            issubclass(C, PG[T])
        with self.assertRaisesRegex(TypeError, no_subscripted_generics):
            issubclass(C, PG[C])

        only_runtime_checkable_protocols = (
            "Instance and class checks can only be used with "
            "@runtime_checkable protocols"
        )

        with self.assertRaisesRegex(TypeError, only_runtime_checkable_protocols):
            issubclass(C, BadP)
        with self.assertRaisesRegex(TypeError, only_runtime_checkable_protocols):
            issubclass(C, BadPG)

        with self.assertRaisesRegex(TypeError, no_subscripted_generics):
            issubclass(P, PG[T])
        with self.assertRaisesRegex(TypeError, no_subscripted_generics):
            issubclass(PG, PG[int])

        only_classes_allowed = r"issubclass\(\) arg 1 must be a class"

        with self.assertRaisesRegex(TypeError, only_classes_allowed):
            issubclass(1, P)
        with self.assertRaisesRegex(TypeError, only_classes_allowed):
            issubclass(1, PG)
        with self.assertRaisesRegex(TypeError, only_classes_allowed):
            issubclass(1, BadP)
        with self.assertRaisesRegex(TypeError, only_classes_allowed):
            issubclass(1, BadPG)

    @skip_if_py312b1
    def test_issubclass_and_isinstance_on_Protocol_itself(self):
        class C:
            def x(self): pass

        self.assertNotIsSubclass(object, Protocol)
        self.assertNotIsInstance(object(), Protocol)

        self.assertNotIsSubclass(str, Protocol)
        self.assertNotIsInstance('foo', Protocol)

        self.assertNotIsSubclass(C, Protocol)
        self.assertNotIsInstance(C(), Protocol)

        only_classes_allowed = r"issubclass\(\) arg 1 must be a class"

        with self.assertRaisesRegex(TypeError, only_classes_allowed):
            issubclass(1, Protocol)
        with self.assertRaisesRegex(TypeError, only_classes_allowed):
            issubclass('foo', Protocol)
        with self.assertRaisesRegex(TypeError, only_classes_allowed):
            issubclass(C(), Protocol)

        T = TypeVar('T')

        @runtime_checkable
        class EmptyProtocol(Protocol): pass

        @runtime_checkable
        class SupportsStartsWith(Protocol):
            def startswith(self, x: str) -> bool: ...

        @runtime_checkable
        class SupportsX(Protocol[T]):
            def x(self): ...

        for proto in EmptyProtocol, SupportsStartsWith, SupportsX:
            with self.subTest(proto=proto.__name__):
                self.assertIsSubclass(proto, Protocol)

        # gh-105237 / PR #105239:
        # check that the presence of Protocol subclasses
        # where `issubclass(X, <subclass>)` evaluates to True
        # doesn't influence the result of `issubclass(X, Protocol)`

        self.assertIsSubclass(object, EmptyProtocol)
        self.assertIsInstance(object(), EmptyProtocol)
        self.assertNotIsSubclass(object, Protocol)
        self.assertNotIsInstance(object(), Protocol)

        self.assertIsSubclass(str, SupportsStartsWith)
        self.assertIsInstance('foo', SupportsStartsWith)
        self.assertNotIsSubclass(str, Protocol)
        self.assertNotIsInstance('foo', Protocol)

        self.assertIsSubclass(C, SupportsX)
        self.assertIsInstance(C(), SupportsX)
        self.assertNotIsSubclass(C, Protocol)
        self.assertNotIsInstance(C(), Protocol)

    def test_protocols_issubclass_non_callable(self):
        class C:
            x = 1

        @runtime_checkable
        class PNonCall(Protocol):
            x = 1

        non_callable_members_illegal = (
            "Protocols with non-method members don't support issubclass()"
        )

        with self.assertRaisesRegex(TypeError, non_callable_members_illegal):
            issubclass(C, PNonCall)

        self.assertIsInstance(C(), PNonCall)
        PNonCall.register(C)

        with self.assertRaisesRegex(TypeError, non_callable_members_illegal):
            issubclass(C, PNonCall)

        self.assertIsInstance(C(), PNonCall)

        # check that non-protocol subclasses are not affected
        class D(PNonCall): ...

        self.assertNotIsSubclass(C, D)
        self.assertNotIsInstance(C(), D)
        D.register(C)
        self.assertIsSubclass(C, D)
        self.assertIsInstance(C(), D)

        with self.assertRaisesRegex(TypeError, non_callable_members_illegal):
            issubclass(D, PNonCall)

    def test_no_weird_caching_with_issubclass_after_isinstance(self):
        @runtime_checkable
        class Spam(Protocol):
            x: int

        class Eggs:
            def __init__(self) -> None:
                self.x = 42

        self.assertIsInstance(Eggs(), Spam)

        # gh-104555: If we didn't override ABCMeta.__subclasscheck__ in _ProtocolMeta,
        # TypeError wouldn't be raised here,
        # as the cached result of the isinstance() check immediately above
        # would mean the issubclass() call would short-circuit
        # before we got to the "raise TypeError" line
        with self.assertRaisesRegex(
            TypeError,
            "Protocols with non-method members don't support issubclass()"
        ):
            issubclass(Eggs, Spam)

    def test_no_weird_caching_with_issubclass_after_isinstance_2(self):
        @runtime_checkable
        class Spam(Protocol):
            x: int

        class Eggs: ...

        self.assertNotIsInstance(Eggs(), Spam)

        # gh-104555: If we didn't override ABCMeta.__subclasscheck__ in _ProtocolMeta,
        # TypeError wouldn't be raised here,
        # as the cached result of the isinstance() check immediately above
        # would mean the issubclass() call would short-circuit
        # before we got to the "raise TypeError" line
        with self.assertRaisesRegex(
            TypeError,
            "Protocols with non-method members don't support issubclass()"
        ):
            issubclass(Eggs, Spam)

    def test_no_weird_caching_with_issubclass_after_isinstance_3(self):
        @runtime_checkable
        class Spam(Protocol):
            x: int

        class Eggs:
            def __getattr__(self, attr):
                if attr == "x":
                    return 42
                raise AttributeError(attr)

        self.assertNotIsInstance(Eggs(), Spam)

        # gh-104555: If we didn't override ABCMeta.__subclasscheck__ in _ProtocolMeta,
        # TypeError wouldn't be raised here,
        # as the cached result of the isinstance() check immediately above
        # would mean the issubclass() call would short-circuit
        # before we got to the "raise TypeError" line
        with self.assertRaisesRegex(
            TypeError,
            "Protocols with non-method members don't support issubclass()"
        ):
            issubclass(Eggs, Spam)

    def test_protocols_isinstance(self):
        T = TypeVar('T')
        @runtime_checkable
        class P(Protocol):
            def meth(x): ...
        @runtime_checkable
        class PG(Protocol[T]):
            def meth(x): ...
        @runtime_checkable
        class WeirdProto(Protocol):
            meth = str.maketrans
        @runtime_checkable
        class WeirdProto2(Protocol):
            meth = lambda *args, **kwargs: None  # noqa: E731
        class CustomCallable:
            def __call__(self, *args, **kwargs):
                pass
        @runtime_checkable
        class WeirderProto(Protocol):
            meth = CustomCallable()
        class BadP(Protocol):
            def meth(x): ...
        class BadPG(Protocol[T]):
            def meth(x): ...
        class C:
            def meth(x): ...
        class C2:
            def __init__(self):
                self.meth = lambda: None
        for klass in C, C2:
            for proto in P, PG, WeirdProto, WeirdProto2, WeirderProto:
                with self.subTest(klass=klass.__name__, proto=proto.__name__):
                    self.assertIsInstance(klass(), proto)

        no_subscripted_generics = (
            "Subscripted generics cannot be used with class and instance checks"
        )

        with self.assertRaisesRegex(TypeError, no_subscripted_generics):
            isinstance(C(), PG[T])
        with self.assertRaisesRegex(TypeError, no_subscripted_generics):
            isinstance(C(), PG[C])

        only_runtime_checkable_msg = (
            "Instance and class checks can only be used "
            "with @runtime_checkable protocols"
        )

        with self.assertRaisesRegex(TypeError, only_runtime_checkable_msg):
            isinstance(C(), BadP)
        with self.assertRaisesRegex(TypeError, only_runtime_checkable_msg):
            isinstance(C(), BadPG)

    def test_protocols_isinstance_properties_and_descriptors(self):
        class C:
            @property
            def attr(self):
                return 42

        class CustomDescriptor:
            def __get__(self, obj, objtype=None):
                return 42

        class D:
            attr = CustomDescriptor()

        # Check that properties set on superclasses
        # are still found by the isinstance() logic
        class E(C): ...
        class F(D): ...

        class Empty: ...

        T = TypeVar('T')

        @runtime_checkable
        class P(Protocol):
            @property
            def attr(self): ...

        @runtime_checkable
        class P1(Protocol):
            attr: int

        @runtime_checkable
        class PG(Protocol[T]):
            @property
            def attr(self): ...

        @runtime_checkable
        class PG1(Protocol[T]):
            attr: T

        @runtime_checkable
        class MethodP(Protocol):
            def attr(self): ...

        @runtime_checkable
        class MethodPG(Protocol[T]):
            def attr(self) -> T: ...

        for protocol_class in P, P1, PG, PG1, MethodP, MethodPG:
            for klass in C, D, E, F:
                with self.subTest(
                    klass=klass.__name__,
                    protocol_class=protocol_class.__name__
                ):
                    self.assertIsInstance(klass(), protocol_class)

            with self.subTest(klass="Empty", protocol_class=protocol_class.__name__):
                self.assertNotIsInstance(Empty(), protocol_class)

        class BadP(Protocol):
            @property
            def attr(self): ...

        class BadP1(Protocol):
            attr: int

        class BadPG(Protocol[T]):
            @property
            def attr(self): ...

        class BadPG1(Protocol[T]):
            attr: T

        cases = (
            PG[T], PG[C], PG1[T], PG1[C], MethodPG[T],
            MethodPG[C], BadP, BadP1, BadPG, BadPG1
        )

        for obj in cases:
            for klass in C, D, E, F, Empty:
                with self.subTest(klass=klass.__name__, obj=obj):
                    with self.assertRaises(TypeError):
                        isinstance(klass(), obj)

    def test_protocols_isinstance_not_fooled_by_custom_dir(self):
        @runtime_checkable
        class HasX(Protocol):
            x: int

        class CustomDirWithX:
            x = 10
            def __dir__(self):
                return []

        class CustomDirWithoutX:
            def __dir__(self):
                return ["x"]

        self.assertIsInstance(CustomDirWithX(), HasX)
        self.assertNotIsInstance(CustomDirWithoutX(), HasX)

    def test_protocols_isinstance_attribute_access_with_side_effects(self):
        class C:
            @property
            def attr(self):
                raise AttributeError('no')

        class CustomDescriptor:
            def __get__(self, obj, objtype=None):
                raise RuntimeError("NO")

        class D:
            attr = CustomDescriptor()

        # Check that properties set on superclasses
        # are still found by the isinstance() logic
        class E(C): ...
        class F(D): ...

        class WhyWouldYouDoThis:
            def __getattr__(self, name):
                raise RuntimeError("wut")

        T = TypeVar('T')

        @runtime_checkable
        class P(Protocol):
            @property
            def attr(self): ...

        @runtime_checkable
        class P1(Protocol):
            attr: int

        @runtime_checkable
        class PG(Protocol[T]):
            @property
            def attr(self): ...

        @runtime_checkable
        class PG1(Protocol[T]):
            attr: T

        @runtime_checkable
        class MethodP(Protocol):
            def attr(self): ...

        @runtime_checkable
        class MethodPG(Protocol[T]):
            def attr(self) -> T: ...

        for protocol_class in P, P1, PG, PG1, MethodP, MethodPG:
            for klass in C, D, E, F:
                with self.subTest(
                    klass=klass.__name__,
                    protocol_class=protocol_class.__name__
                ):
                    self.assertIsInstance(klass(), protocol_class)

            with self.subTest(
                klass="WhyWouldYouDoThis",
                protocol_class=protocol_class.__name__
            ):
                self.assertNotIsInstance(WhyWouldYouDoThis(), protocol_class)

    def test_protocols_isinstance___slots__(self):
        # As per the consensus in https://github.com/python/typing/issues/1367,
        # this is desirable behaviour
        @runtime_checkable
        class HasX(Protocol):
            x: int

        class HasNothingButSlots:
            __slots__ = ("x",)

        self.assertIsInstance(HasNothingButSlots(), HasX)

    def test_protocols_isinstance_py36(self):
        class APoint:
            def __init__(self, x, y, label):
                self.x = x
                self.y = y
                self.label = label
        class BPoint:
            label = 'B'
            def __init__(self, x, y):
                self.x = x
                self.y = y
        class C:
            def __init__(self, attr):
                self.attr = attr
            def meth(self, arg):
                return 0
        class Bad: pass
        self.assertIsInstance(APoint(1, 2, 'A'), Point)
        self.assertIsInstance(BPoint(1, 2), Point)
        self.assertNotIsInstance(MyPoint(), Point)
        self.assertIsInstance(BPoint(1, 2), Position)
        self.assertIsInstance(Other(), Proto)
        self.assertIsInstance(Concrete(), Proto)
        self.assertIsInstance(C(42), Proto)
        self.assertNotIsInstance(Bad(), Proto)
        self.assertNotIsInstance(Bad(), Point)
        self.assertNotIsInstance(Bad(), Position)
        self.assertNotIsInstance(Bad(), Concrete)
        self.assertNotIsInstance(Other(), Concrete)
        self.assertIsInstance(NT(1, 2), Position)

    def test_protocols_isinstance_init(self):
        T = TypeVar('T')
        @runtime_checkable
        class P(Protocol):
            x = 1
        @runtime_checkable
        class PG(Protocol[T]):
            x = 1
        class C:
            def __init__(self, x):
                self.x = x
        self.assertIsInstance(C(1), P)
        self.assertIsInstance(C(1), PG)

    def test_protocols_isinstance_monkeypatching(self):
        @runtime_checkable
        class HasX(Protocol):
            x: int

        class Foo: ...

        f = Foo()
        self.assertNotIsInstance(f, HasX)
        f.x = 42
        self.assertIsInstance(f, HasX)
        del f.x
        self.assertNotIsInstance(f, HasX)

    @skip_if_py312b1
    def test_runtime_checkable_generic_non_protocol(self):
        # Make sure this doesn't raise AttributeError
        with self.assertRaisesRegex(
            TypeError,
            "@runtime_checkable can be only applied to protocol classes",
        ):
            @runtime_checkable
            class Foo(Generic[T]): ...

    def test_runtime_checkable_generic(self):
        @runtime_checkable
        class Foo(Protocol[T]):
            def meth(self) -> T: ...

        class Impl:
            def meth(self) -> int: ...

        self.assertIsSubclass(Impl, Foo)

        class NotImpl:
            def method(self) -> int: ...

        self.assertNotIsSubclass(NotImpl, Foo)

    if sys.version_info >= (3, 12):
        exec(textwrap.dedent(
            """
            @skip_if_py312b1
            def test_pep695_generics_can_be_runtime_checkable(self):
                @runtime_checkable
                class HasX(Protocol):
                    x: int

                class Bar[T]:
                    x: T
                    def __init__(self, x):
                        self.x = x

                class Capybara[T]:
                    y: str
                    def __init__(self, y):
                        self.y = y

                self.assertIsInstance(Bar(1), HasX)
                self.assertNotIsInstance(Capybara('a'), HasX)
                """
        ))

    @skip_if_py312b1
    def test_protocols_isinstance_generic_classes(self):
        T = TypeVar("T")

        class Foo(Generic[T]):
            x: T

            def __init__(self, x):
                self.x = x

        class Bar(Foo[int]):
            ...

        @runtime_checkable
        class HasX(Protocol):
            x: int

        foo = Foo(1)
        self.assertIsInstance(foo, HasX)

        bar = Bar(2)
        self.assertIsInstance(bar, HasX)

    def test_protocols_support_register(self):
        @runtime_checkable
        class P(Protocol):
            x = 1
        class PM(Protocol):
            def meth(self): pass
        class D(PM): pass
        class C: pass
        D.register(C)
        P.register(C)
        self.assertIsInstance(C(), P)
        self.assertIsInstance(C(), D)

    def test_none_on_non_callable_doesnt_block_implementation(self):
        @runtime_checkable
        class P(Protocol):
            x = 1
        class A:
            x = 1
        class B(A):
            x = None
        class C:
            def __init__(self):
                self.x = None
        self.assertIsInstance(B(), P)
        self.assertIsInstance(C(), P)

    def test_none_on_callable_blocks_implementation(self):
        @runtime_checkable
        class P(Protocol):
            def x(self): ...
        class A:
            def x(self): ...
        class B(A):
            x = None
        class C:
            def __init__(self):
                self.x = None
        self.assertNotIsInstance(B(), P)
        self.assertNotIsInstance(C(), P)

    def test_non_protocol_subclasses(self):
        class P(Protocol):
            x = 1
        @runtime_checkable
        class PR(Protocol):
            def meth(self): pass
        class NonP(P):
            x = 1
        class NonPR(PR): pass
        class C(metaclass=abc.ABCMeta):
            x = 1
        class D(metaclass=abc.ABCMeta):  # noqa: B024
            def meth(self): pass  # noqa: B027
        self.assertNotIsInstance(C(), NonP)
        self.assertNotIsInstance(D(), NonPR)
        self.assertNotIsSubclass(C, NonP)
        self.assertNotIsSubclass(D, NonPR)
        self.assertIsInstance(NonPR(), PR)
        self.assertIsSubclass(NonPR, PR)

        self.assertNotIn("__protocol_attrs__", vars(NonP))
        self.assertNotIn("__protocol_attrs__", vars(NonPR))
        self.assertNotIn("__callable_proto_members_only__", vars(NonP))
        self.assertNotIn("__callable_proto_members_only__", vars(NonPR))

        acceptable_extra_attrs = {
            '_is_protocol', '_is_runtime_protocol', '__parameters__',
            '__init__', '__annotations__', '__subclasshook__',
        }
        self.assertLessEqual(vars(NonP).keys(), vars(C).keys() | acceptable_extra_attrs)
        self.assertLessEqual(
            vars(NonPR).keys(), vars(D).keys() | acceptable_extra_attrs
        )

    def test_custom_subclasshook(self):
        class P(Protocol):
            x = 1
        class OKClass: pass
        class BadClass:
            x = 1
        class C(P):
            @classmethod
            def __subclasshook__(cls, other):
                return other.__name__.startswith("OK")
        self.assertIsInstance(OKClass(), C)
        self.assertNotIsInstance(BadClass(), C)
        self.assertIsSubclass(OKClass, C)
        self.assertNotIsSubclass(BadClass, C)

    @skip_if_py312b1
    def test_issubclass_fails_correctly(self):
        @runtime_checkable
        class P(Protocol):
            x = 1
        class C: pass
        with self.assertRaisesRegex(TypeError, r"issubclass\(\) arg 1 must be a class"):
            issubclass(C(), P)

    def test_defining_generic_protocols(self):
        T = TypeVar('T')
        S = TypeVar('S')
        @runtime_checkable
        class PR(Protocol[T, S]):
            def meth(self): pass
        class P(PR[int, T], Protocol[T]):
            y = 1
        with self.assertRaises(TypeError):
            issubclass(PR[int, T], PR)
        with self.assertRaises(TypeError):
            issubclass(P[str], PR)
        with self.assertRaises(TypeError):
            PR[int]
        with self.assertRaises(TypeError):
            P[int, str]
        if not TYPING_3_10_0:
            with self.assertRaises(TypeError):
                PR[int, 1]
            with self.assertRaises(TypeError):
                PR[int, ClassVar]
        class C(PR[int, T]): pass
        self.assertIsInstance(C[str](), C)

    def test_defining_generic_protocols_old_style(self):
        T = TypeVar('T')
        S = TypeVar('S')
        @runtime_checkable
        class PR(Protocol, Generic[T, S]):
            def meth(self): pass
        class P(PR[int, str], Protocol):
            y = 1
        with self.assertRaises(TypeError):
            self.assertIsSubclass(PR[int, str], PR)
        self.assertIsSubclass(P, PR)
        with self.assertRaises(TypeError):
            PR[int]
        if not TYPING_3_10_0:
            with self.assertRaises(TypeError):
                PR[int, 1]
        class P1(Protocol, Generic[T]):
            def bar(self, x: T) -> str: ...
        class P2(Generic[T], Protocol):
            def bar(self, x: T) -> str: ...
        @runtime_checkable
        class PSub(P1[str], Protocol):
            x = 1
        class Test:
            x = 1
            def bar(self, x: str) -> str:
                return x
        self.assertIsInstance(Test(), PSub)
        if not TYPING_3_10_0:
            with self.assertRaises(TypeError):
                PR[int, ClassVar]

    if hasattr(typing, "TypeAliasType"):
        exec(textwrap.dedent(
            """
            def test_pep695_generic_protocol_callable_members(self):
                @runtime_checkable
                class Foo[T](Protocol):
                    def meth(self, x: T) -> None: ...

                class Bar[T]:
                    def meth(self, x: T) -> None: ...

                self.assertIsInstance(Bar(), Foo)
                self.assertIsSubclass(Bar, Foo)

                @runtime_checkable
                class SupportsTrunc[T](Protocol):
                    def __trunc__(self) -> T: ...

                self.assertIsInstance(0.0, SupportsTrunc)
                self.assertIsSubclass(float, SupportsTrunc)

            def test_no_weird_caching_with_issubclass_after_isinstance_pep695(self):
                @runtime_checkable
                class Spam[T](Protocol):
                    x: T

                class Eggs[T]:
                    def __init__(self, x: T) -> None:
                        self.x = x

                self.assertIsInstance(Eggs(42), Spam)

                # gh-104555: If we didn't override ABCMeta.__subclasscheck__ in _ProtocolMeta,
                # TypeError wouldn't be raised here,
                # as the cached result of the isinstance() check immediately above
                # would mean the issubclass() call would short-circuit
                # before we got to the "raise TypeError" line
                with self.assertRaises(TypeError):
                    issubclass(Eggs, Spam)
            """
        ))

    def test_init_called(self):
        T = TypeVar('T')
        class P(Protocol[T]): pass
        class C(P[T]):
            def __init__(self):
                self.test = 'OK'
        self.assertEqual(C[int]().test, 'OK')

    def test_protocols_bad_subscripts(self):
        T = TypeVar('T')
        S = TypeVar('S')
        with self.assertRaises(TypeError):
            class P(Protocol[T, T]): pass
        with self.assertRaises(TypeError):
            class P(Protocol[int]): pass
        with self.assertRaises(TypeError):
            class P(Protocol[T], Protocol[S]): pass
        with self.assertRaises(TypeError):
            class P(typing.Mapping[T, S], Protocol[T]): pass

    def test_generic_protocols_repr(self):
        T = TypeVar('T')
        S = TypeVar('S')
        class P(Protocol[T, S]): pass
        self.assertTrue(repr(P[T, S]).endswith('P[~T, ~S]'))
        self.assertTrue(repr(P[int, str]).endswith('P[int, str]'))

    def test_generic_protocols_eq(self):
        T = TypeVar('T')
        S = TypeVar('S')
        class P(Protocol[T, S]): pass
        self.assertEqual(P, P)
        self.assertEqual(P[int, T], P[int, T])
        self.assertEqual(P[T, T][Tuple[T, S]][int, str],
                         P[Tuple[int, str], Tuple[int, str]])

    def test_generic_protocols_special_from_generic(self):
        T = TypeVar('T')
        class P(Protocol[T]): pass
        self.assertEqual(P.__parameters__, (T,))
        self.assertEqual(P[int].__parameters__, ())
        self.assertEqual(P[int].__args__, (int,))
        self.assertIs(P[int].__origin__, P)

    def test_generic_protocols_special_from_protocol(self):
        @runtime_checkable
        class PR(Protocol):
            x = 1
        class P(Protocol):
            def meth(self):
                pass
        T = TypeVar('T')
        class PG(Protocol[T]):
            x = 1
            def meth(self):
                pass
        self.assertTrue(P._is_protocol)
        self.assertTrue(PR._is_protocol)
        self.assertTrue(PG._is_protocol)
        self.assertFalse(P._is_runtime_protocol)
        self.assertTrue(PR._is_runtime_protocol)
        self.assertTrue(PG[int]._is_protocol)
        self.assertEqual(typing_extensions._get_protocol_attrs(P), {'meth'})
        self.assertEqual(typing_extensions._get_protocol_attrs(PR), {'x'})
        self.assertEqual(frozenset(typing_extensions._get_protocol_attrs(PG)),
                         frozenset({'x', 'meth'}))

    def test_no_runtime_deco_on_nominal(self):
        with self.assertRaises(TypeError):
            @runtime_checkable
            class C: pass
        class Proto(Protocol):
            x = 1
        with self.assertRaises(TypeError):
            @runtime_checkable
            class Concrete(Proto):
                pass

    def test_none_treated_correctly(self):
        @runtime_checkable
        class P(Protocol):
            x: int = None
        class B(object): pass
        self.assertNotIsInstance(B(), P)
        class C:
            x = 1
        class D:
            x = None
        self.assertIsInstance(C(), P)
        self.assertIsInstance(D(), P)
        class CI:
            def __init__(self):
                self.x = 1
        class DI:
            def __init__(self):
                self.x = None
        self.assertIsInstance(CI(), P)
        self.assertIsInstance(DI(), P)

    def test_protocols_in_unions(self):
        class P(Protocol):
            x: int = None
        Alias = typing.Union[typing.Iterable, P]
        Alias2 = typing.Union[P, typing.Iterable]
        self.assertEqual(Alias, Alias2)

    def test_protocols_pickleable(self):
        global P, CP  # pickle wants to reference the class by name
        T = TypeVar('T')

        @runtime_checkable
        class P(Protocol[T]):
            x = 1
        class CP(P[int]):
            pass

        c = CP()
        c.foo = 42
        c.bar = 'abc'
        for proto in range(pickle.HIGHEST_PROTOCOL + 1):
            z = pickle.dumps(c, proto)
            x = pickle.loads(z)
            self.assertEqual(x.foo, 42)
            self.assertEqual(x.bar, 'abc')
            self.assertEqual(x.x, 1)
            self.assertEqual(x.__dict__, {'foo': 42, 'bar': 'abc'})
            s = pickle.dumps(P)
            D = pickle.loads(s)
            class E:
                x = 1
            self.assertIsInstance(E(), D)

    def test_collections_protocols_allowed(self):
        @runtime_checkable
        class Custom(collections.abc.Iterable, Protocol):
            def close(self): pass

        class A: ...
        class B:
            def __iter__(self):
                return []
            def close(self):
                return 0

        self.assertIsSubclass(B, Custom)
        self.assertNotIsSubclass(A, Custom)

    def test_builtin_protocol_allowlist(self):
        with self.assertRaises(TypeError):
            class CustomProtocol(TestCase, Protocol):
                pass

        class CustomContextManager(typing.ContextManager, Protocol):
            pass

    def test_non_runtime_protocol_isinstance_check(self):
        class P(Protocol):
            x: int

        with self.assertRaisesRegex(TypeError, "@runtime_checkable"):
            isinstance(1, P)

    def test_no_init_same_for_different_protocol_implementations(self):
        class CustomProtocolWithoutInitA(Protocol):
            pass

        class CustomProtocolWithoutInitB(Protocol):
            pass

        self.assertEqual(CustomProtocolWithoutInitA.__init__, CustomProtocolWithoutInitB.__init__)

    def test_protocol_generic_over_paramspec(self):
        P = ParamSpec("P")
        T = TypeVar("T")
        T2 = TypeVar("T2")

        class MemoizedFunc(Protocol[P, T, T2]):
            cache: typing.Dict[T2, T]
            def __call__(self, *args: P.args, **kwargs: P.kwargs) -> T: ...

        self.assertEqual(MemoizedFunc.__parameters__, (P, T, T2))
        self.assertTrue(MemoizedFunc._is_protocol)

        with self.assertRaises(TypeError):
            MemoizedFunc[[int, str, str]]

        if sys.version_info >= (3, 10):
            # These unfortunately don't pass on <=3.9,
            # due to typing._type_check on older Python versions
            X = MemoizedFunc[[int, str, str], T, T2]
            self.assertEqual(X.__parameters__, (T, T2))
            self.assertEqual(X.__args__, ((int, str, str), T, T2))

            Y = X[bytes, memoryview]
            self.assertEqual(Y.__parameters__, ())
            self.assertEqual(Y.__args__, ((int, str, str), bytes, memoryview))

    def test_protocol_generic_over_typevartuple(self):
        Ts = TypeVarTuple("Ts")
        T = TypeVar("T")
        T2 = TypeVar("T2")

        class MemoizedFunc(Protocol[Unpack[Ts], T, T2]):
            cache: typing.Dict[T2, T]
            def __call__(self, *args: Unpack[Ts]) -> T: ...

        self.assertEqual(MemoizedFunc.__parameters__, (Ts, T, T2))
        self.assertTrue(MemoizedFunc._is_protocol)

        things = "arguments" if sys.version_info >= (3, 11) else "parameters"

        # A bug was fixed in 3.11.1
        # (https://github.com/python/cpython/commit/74920aa27d0c57443dd7f704d6272cca9c507ab3)
        # That means this assertion doesn't pass on 3.11.0,
        # but it passes on all other Python versions
        if sys.version_info[:3] != (3, 11, 0):
            with self.assertRaisesRegex(TypeError, f"Too few {things}"):
                MemoizedFunc[int]

        X = MemoizedFunc[int, T, T2]
        self.assertEqual(X.__parameters__, (T, T2))
        self.assertEqual(X.__args__, (int, T, T2))

        Y = X[bytes, memoryview]
        self.assertEqual(Y.__parameters__, ())
        self.assertEqual(Y.__args__, (int, bytes, memoryview))

    @skip_if_py312b1
    def test_interaction_with_isinstance_checks_on_superclasses_with_ABCMeta(self):
        # Ensure the cache is empty, or this test won't work correctly
        collections.abc.Sized._abc_registry_clear()

        class Foo(collections.abc.Sized, Protocol): pass

        # CPython gh-105144: this previously raised TypeError
        # if a Protocol subclass of Sized had been created
        # before any isinstance() checks against Sized
        self.assertNotIsInstance(1, collections.abc.Sized)

    @skip_if_py312b1
    def test_interaction_with_isinstance_checks_on_superclasses_with_ABCMeta_2(self):
        # Ensure the cache is empty, or this test won't work correctly
        collections.abc.Sized._abc_registry_clear()

        class Foo(typing.Sized, Protocol): pass

        # CPython gh-105144: this previously raised TypeError
        # if a Protocol subclass of Sized had been created
        # before any isinstance() checks against Sized
        self.assertNotIsInstance(1, typing.Sized)


class Point2DGeneric(Generic[T], TypedDict):
    a: T
    b: T


class Bar(Foo):
    b: int


class BarGeneric(FooGeneric[T], total=False):
    b: int


class TypedDictTests(BaseTestCase):

    def test_basics_iterable_syntax(self):
        Emp = TypedDict('Emp', {'name': str, 'id': int})
        self.assertIsSubclass(Emp, dict)
        self.assertIsSubclass(Emp, typing.MutableMapping)
        self.assertNotIsSubclass(Emp, collections.abc.Sequence)
        jim = Emp(name='Jim', id=1)
        self.assertIs(type(jim), dict)
        self.assertEqual(jim['name'], 'Jim')
        self.assertEqual(jim['id'], 1)
        self.assertEqual(Emp.__name__, 'Emp')
        self.assertEqual(Emp.__module__, __name__)
        self.assertEqual(Emp.__bases__, (dict,))
        self.assertEqual(Emp.__annotations__, {'name': str, 'id': int})
        self.assertEqual(Emp.__total__, True)

    @skipIf(sys.version_info < (3, 13), "Change in behavior in 3.13")
    def test_keywords_syntax_raises_on_3_13(self):
        with self.assertRaises(TypeError):
            Emp = TypedDict('Emp', name=str, id=int)

    @skipIf(sys.version_info >= (3, 13), "3.13 removes support for kwargs")
    def test_basics_keywords_syntax(self):
        with self.assertWarns(DeprecationWarning):
            Emp = TypedDict('Emp', name=str, id=int)
        self.assertIsSubclass(Emp, dict)
        self.assertIsSubclass(Emp, typing.MutableMapping)
        self.assertNotIsSubclass(Emp, collections.abc.Sequence)
        jim = Emp(name='Jim', id=1)
        self.assertIs(type(jim), dict)
        self.assertEqual(jim['name'], 'Jim')
        self.assertEqual(jim['id'], 1)
        self.assertEqual(Emp.__name__, 'Emp')
        self.assertEqual(Emp.__module__, __name__)
        self.assertEqual(Emp.__bases__, (dict,))
        self.assertEqual(Emp.__annotations__, {'name': str, 'id': int})
        self.assertEqual(Emp.__total__, True)

    @skipIf(sys.version_info >= (3, 13), "3.13 removes support for kwargs")
    def test_typeddict_special_keyword_names(self):
        with self.assertWarns(DeprecationWarning):
            TD = TypedDict("TD", cls=type, self=object, typename=str, _typename=int,
                           fields=list, _fields=dict)
        self.assertEqual(TD.__name__, 'TD')
        self.assertEqual(TD.__annotations__, {'cls': type, 'self': object, 'typename': str,
                                              '_typename': int, 'fields': list, '_fields': dict})
        a = TD(cls=str, self=42, typename='foo', _typename=53,
               fields=[('bar', tuple)], _fields={'baz', set})
        self.assertEqual(a['cls'], str)
        self.assertEqual(a['self'], 42)
        self.assertEqual(a['typename'], 'foo')
        self.assertEqual(a['_typename'], 53)
        self.assertEqual(a['fields'], [('bar', tuple)])
        self.assertEqual(a['_fields'], {'baz', set})

    @skipIf(hasattr(typing, 'TypedDict'), "Should be tested by upstream")
    def test_typeddict_create_errors(self):
        with self.assertRaises(TypeError):
            TypedDict.__new__()
        with self.assertRaises(TypeError):
            TypedDict()
        with self.assertRaises(TypeError):
            TypedDict('Emp', [('name', str)], None)

        with self.assertWarns(DeprecationWarning):
            Emp = TypedDict(_typename='Emp', name=str, id=int)
        self.assertEqual(Emp.__name__, 'Emp')
        self.assertEqual(Emp.__annotations__, {'name': str, 'id': int})

        with self.assertWarns(DeprecationWarning):
            Emp = TypedDict('Emp', _fields={'name': str, 'id': int})
        self.assertEqual(Emp.__name__, 'Emp')
        self.assertEqual(Emp.__annotations__, {'name': str, 'id': int})

    def test_typeddict_errors(self):
        Emp = TypedDict('Emp', {'name': str, 'id': int})
        if sys.version_info >= (3, 12):
            self.assertEqual(TypedDict.__module__, 'typing')
        else:
            self.assertEqual(TypedDict.__module__, 'typing_extensions')
        jim = Emp(name='Jim', id=1)
        with self.assertRaises(TypeError):
            isinstance({}, Emp)
        with self.assertRaises(TypeError):
            isinstance(jim, Emp)
        with self.assertRaises(TypeError):
            issubclass(dict, Emp)

        if not TYPING_3_11_0:
            with self.assertRaises(TypeError), self.assertWarns(DeprecationWarning):
                TypedDict('Hi', x=1)
            with self.assertRaises(TypeError):
                TypedDict('Hi', [('x', int), ('y', 1)])
        with self.assertRaises(TypeError):
            TypedDict('Hi', [('x', int)], y=int)

    def test_py36_class_syntax_usage(self):
        self.assertEqual(LabelPoint2D.__name__, 'LabelPoint2D')
        self.assertEqual(LabelPoint2D.__module__, __name__)
        self.assertEqual(get_type_hints(LabelPoint2D), {'x': int, 'y': int, 'label': str})
        self.assertEqual(LabelPoint2D.__bases__, (dict,))
        self.assertEqual(LabelPoint2D.__total__, True)
        self.assertNotIsSubclass(LabelPoint2D, typing.Sequence)
        not_origin = Point2D(x=0, y=1)
        self.assertEqual(not_origin['x'], 0)
        self.assertEqual(not_origin['y'], 1)
        other = LabelPoint2D(x=0, y=1, label='hi')
        self.assertEqual(other['label'], 'hi')

    def test_pickle(self):
        global EmpD  # pickle wants to reference the class by name
        EmpD = TypedDict('EmpD', {"name": str, "id": int})
        jane = EmpD({'name': 'jane', 'id': 37})
        point = Point2DGeneric(a=5.0, b=3.0)
        for proto in range(pickle.HIGHEST_PROTOCOL + 1):
            # Test non-generic TypedDict
            z = pickle.dumps(jane, proto)
            jane2 = pickle.loads(z)
            self.assertEqual(jane2, jane)
            self.assertEqual(jane2, {'name': 'jane', 'id': 37})
            ZZ = pickle.dumps(EmpD, proto)
            EmpDnew = pickle.loads(ZZ)
            self.assertEqual(EmpDnew({'name': 'jane', 'id': 37}), jane)
            # and generic TypedDict
            y = pickle.dumps(point, proto)
            point2 = pickle.loads(y)
            self.assertEqual(point, point2)
            self.assertEqual(point2, {'a': 5.0, 'b': 3.0})
            YY = pickle.dumps(Point2DGeneric, proto)
            Point2DGenericNew = pickle.loads(YY)
            self.assertEqual(Point2DGenericNew({'a': 5.0, 'b': 3.0}), point)

    def test_optional(self):
        EmpD = TypedDict('EmpD', {"name": str, "id": int})

        self.assertEqual(typing.Optional[EmpD], typing.Union[None, EmpD])
        self.assertNotEqual(typing.List[EmpD], typing.Tuple[EmpD])

    def test_total(self):
        D = TypedDict('D', {'x': int}, total=False)
        self.assertEqual(D(), {})
        self.assertEqual(D(x=1), {'x': 1})
        self.assertEqual(D.__total__, False)
        self.assertEqual(D.__required_keys__, frozenset())
        self.assertEqual(D.__optional_keys__, {'x'})

        self.assertEqual(Options(), {})
        self.assertEqual(Options(log_level=2), {'log_level': 2})
        self.assertEqual(Options.__total__, False)
        self.assertEqual(Options.__required_keys__, frozenset())
        self.assertEqual(Options.__optional_keys__, {'log_level', 'log_path'})

    def test_optional_keys(self):
        assert Point2Dor3D.__required_keys__ == frozenset(['x', 'y'])
        assert Point2Dor3D.__optional_keys__ == frozenset(['z'])

    def test_required_notrequired_keys(self):
        assert NontotalMovie.__required_keys__ == frozenset({'title'})
        assert NontotalMovie.__optional_keys__ == frozenset({'year'})

        assert TotalMovie.__required_keys__ == frozenset({'title'})
        assert TotalMovie.__optional_keys__ == frozenset({'year'})


    def test_keys_inheritance(self):
        assert BaseAnimal.__required_keys__ == frozenset(['name'])
        assert BaseAnimal.__optional_keys__ == frozenset([])
        assert get_type_hints(BaseAnimal) == {'name': str}

        assert Animal.__required_keys__ == frozenset(['name'])
        assert Animal.__optional_keys__ == frozenset(['tail', 'voice'])
        assert get_type_hints(Animal) == {
            'name': str,
            'tail': bool,
            'voice': str,
        }

        assert Cat.__required_keys__ == frozenset(['name', 'fur_color'])
        assert Cat.__optional_keys__ == frozenset(['tail', 'voice'])
        assert get_type_hints(Cat) == {
            'fur_color': str,
            'name': str,
            'tail': bool,
            'voice': str,
        }

    def test_is_typeddict(self):
        assert is_typeddict(Point2D) is True
        assert is_typeddict(Point2Dor3D) is True
        assert is_typeddict(Union[str, int]) is False
        # classes, not instances
        assert is_typeddict(Point2D()) is False

    @skipUnless(TYPING_3_8_0, "Python 3.8+ required")
    def test_is_typeddict_against_typeddict_from_typing(self):
        Point = typing.TypedDict('Point', {'x': int, 'y': int})

        class PointDict2D(typing.TypedDict):
            x: int
            y: int

        class PointDict3D(PointDict2D, total=False):
            z: int

        assert is_typeddict(Point) is True
        assert is_typeddict(PointDict2D) is True
        assert is_typeddict(PointDict3D) is True

    @skipUnless(HAS_FORWARD_MODULE, "ForwardRef.__forward_module__ was added in 3.9")
    def test_get_type_hints_cross_module_subclass(self):
        self.assertNotIn("_DoNotImport", globals())
        self.assertEqual(
            {k: v.__name__ for k, v in get_type_hints(Bar).items()},
            {'a': "_DoNotImport", 'b': "int"}
        )

    def test_get_type_hints_generic(self):
        self.assertEqual(
            get_type_hints(BarGeneric),
            {'a': typing.Optional[T], 'b': int}
        )

        class FooBarGeneric(BarGeneric[int]):
            c: str

        self.assertEqual(
            get_type_hints(FooBarGeneric),
            {'a': typing.Optional[T], 'b': int, 'c': str}
        )

    def test_generic_inheritance(self):
        class A(TypedDict, Generic[T]):
            a: T

        self.assertEqual(A.__bases__, (Generic, dict))
        self.assertEqual(A.__orig_bases__, (TypedDict, Generic[T]))
        self.assertEqual(A.__mro__, (A, Generic, dict, object))
        self.assertEqual(A.__parameters__, (T,))
        self.assertEqual(A[str].__parameters__, ())
        self.assertEqual(A[str].__args__, (str,))

        class A2(Generic[T], TypedDict):
            a: T

        self.assertEqual(A2.__bases__, (Generic, dict))
        self.assertEqual(A2.__orig_bases__, (Generic[T], TypedDict))
        self.assertEqual(A2.__mro__, (A2, Generic, dict, object))
        self.assertEqual(A2.__parameters__, (T,))
        self.assertEqual(A2[str].__parameters__, ())
        self.assertEqual(A2[str].__args__, (str,))

        class B(A[KT], total=False):
            b: KT

        self.assertEqual(B.__bases__, (Generic, dict))
        self.assertEqual(B.__orig_bases__, (A[KT],))
        self.assertEqual(B.__mro__, (B, Generic, dict, object))
        self.assertEqual(B.__parameters__, (KT,))
        self.assertEqual(B.__total__, False)
        self.assertEqual(B.__optional_keys__, frozenset(['b']))
        self.assertEqual(B.__required_keys__, frozenset(['a']))

        self.assertEqual(B[str].__parameters__, ())
        self.assertEqual(B[str].__args__, (str,))
        self.assertEqual(B[str].__origin__, B)

        class C(B[int]):
            c: int

        self.assertEqual(C.__bases__, (Generic, dict))
        self.assertEqual(C.__orig_bases__, (B[int],))
        self.assertEqual(C.__mro__, (C, Generic, dict, object))
        self.assertEqual(C.__parameters__, ())
        self.assertEqual(C.__total__, True)
        self.assertEqual(C.__optional_keys__, frozenset(['b']))
        self.assertEqual(C.__required_keys__, frozenset(['a', 'c']))
        assert C.__annotations__ == {
            'a': T,
            'b': KT,
            'c': int,
        }
        with self.assertRaises(TypeError):
            C[str]


        class Point3D(Point2DGeneric[T], Generic[T, KT]):
            c: KT

        self.assertEqual(Point3D.__bases__, (Generic, dict))
        self.assertEqual(Point3D.__orig_bases__, (Point2DGeneric[T], Generic[T, KT]))
        self.assertEqual(Point3D.__mro__, (Point3D, Generic, dict, object))
        self.assertEqual(Point3D.__parameters__, (T, KT))
        self.assertEqual(Point3D.__total__, True)
        self.assertEqual(Point3D.__optional_keys__, frozenset())
        self.assertEqual(Point3D.__required_keys__, frozenset(['a', 'b', 'c']))
        assert Point3D.__annotations__ == {
            'a': T,
            'b': T,
            'c': KT,
        }
        self.assertEqual(Point3D[int, str].__origin__, Point3D)

        with self.assertRaises(TypeError):
            Point3D[int]

        with self.assertRaises(TypeError):
            class Point3D(Point2DGeneric[T], Generic[KT]):
                c: KT

    def test_implicit_any_inheritance(self):
        class A(TypedDict, Generic[T]):
            a: T

        class B(A[KT], total=False):
            b: KT

        class WithImplicitAny(B):
            c: int

        self.assertEqual(WithImplicitAny.__bases__, (Generic, dict,))
        self.assertEqual(WithImplicitAny.__mro__, (WithImplicitAny, Generic, dict, object))
        # Consistent with GenericTests.test_implicit_any
        self.assertEqual(WithImplicitAny.__parameters__, ())
        self.assertEqual(WithImplicitAny.__total__, True)
        self.assertEqual(WithImplicitAny.__optional_keys__, frozenset(['b']))
        self.assertEqual(WithImplicitAny.__required_keys__, frozenset(['a', 'c']))
        assert WithImplicitAny.__annotations__ == {
            'a': T,
            'b': KT,
            'c': int,
        }
        with self.assertRaises(TypeError):
            WithImplicitAny[str]


class AnnotatedTests(BaseTestCase):

    def test_repr(self):
        if hasattr(typing, 'Annotated'):
            mod_name = 'typing'
        else:
            mod_name = "typing_extensions"
        self.assertEqual(
            repr(Annotated[int, 4, 5]),
            mod_name + ".Annotated[int, 4, 5]"
        )
        self.assertEqual(
            repr(Annotated[List[int], 4, 5]),
            mod_name + ".Annotated[typing.List[int], 4, 5]"
        )

    def test_flatten(self):
        A = Annotated[Annotated[int, 4], 5]
        self.assertEqual(A, Annotated[int, 4, 5])
        self.assertEqual(A.__metadata__, (4, 5))
        self.assertEqual(A.__origin__, int)

    def test_specialize(self):
        L = Annotated[List[T], "my decoration"]
        LI = Annotated[List[int], "my decoration"]
        self.assertEqual(L[int], Annotated[List[int], "my decoration"])
        self.assertEqual(L[int].__metadata__, ("my decoration",))
        self.assertEqual(L[int].__origin__, List[int])
        with self.assertRaises(TypeError):
            LI[int]
        with self.assertRaises(TypeError):
            L[int, float]

    def test_hash_eq(self):
        self.assertEqual(len({Annotated[int, 4, 5], Annotated[int, 4, 5]}), 1)
        self.assertNotEqual(Annotated[int, 4, 5], Annotated[int, 5, 4])
        self.assertNotEqual(Annotated[int, 4, 5], Annotated[str, 4, 5])
        self.assertNotEqual(Annotated[int, 4], Annotated[int, 4, 4])
        self.assertEqual(
            {Annotated[int, 4, 5], Annotated[int, 4, 5], Annotated[T, 4, 5]},
            {Annotated[int, 4, 5], Annotated[T, 4, 5]}
        )

    def test_instantiate(self):
        class C:
            classvar = 4

            def __init__(self, x):
                self.x = x

            def __eq__(self, other):
                if not isinstance(other, C):
                    return NotImplemented
                return other.x == self.x

        A = Annotated[C, "a decoration"]
        a = A(5)
        c = C(5)
        self.assertEqual(a, c)
        self.assertEqual(a.x, c.x)
        self.assertEqual(a.classvar, c.classvar)

    def test_instantiate_generic(self):
        self.assertEqual(collections.Counter([4, 4, 5]), {4: 2, 5: 1})

    def test_cannot_instantiate_forward(self):
        A = Annotated["int", (5, 6)]
        with self.assertRaises(TypeError):
            A(5)

    def test_cannot_instantiate_type_var(self):
        A = Annotated[T, (5, 6)]
        with self.assertRaises(TypeError):
            A(5)

    def test_cannot_getattr_typevar(self):
        with self.assertRaises(AttributeError):
            Annotated[T, (5, 7)].x

    def test_attr_passthrough(self):
        class C:
            classvar = 4

        A = Annotated[C, "a decoration"]
        self.assertEqual(A.classvar, 4)
        A.x = 5
        self.assertEqual(C.x, 5)

    @skipIf(sys.version_info[:2] in ((3, 9), (3, 10)), "Waiting for bpo-46491 bugfix.")
    def test_special_form_containment(self):
        class C:
            classvar: Annotated[ClassVar[int], "a decoration"] = 4
            const: Annotated[Final[int], "Const"] = 4

        if sys.version_info[:2] >= (3, 7):
            self.assertEqual(get_type_hints(C, globals())["classvar"], ClassVar[int])
            self.assertEqual(get_type_hints(C, globals())["const"], Final[int])
        else:
            self.assertEqual(
                get_type_hints(C, globals())["classvar"],
                Annotated[ClassVar[int], "a decoration"]
            )
            self.assertEqual(
                get_type_hints(C, globals())["const"], Annotated[Final[int], "Const"]
            )

    def test_cannot_subclass(self):
        with self.assertRaisesRegex(TypeError, "Cannot subclass .*Annotated"):
            class C(Annotated):
                pass

    def test_cannot_check_instance(self):
        with self.assertRaises(TypeError):
            isinstance(5, Annotated[int, "positive"])

    def test_cannot_check_subclass(self):
        with self.assertRaises(TypeError):
            issubclass(int, Annotated[int, "positive"])

    def test_pickle(self):
        samples = [typing.Any, typing.Union[int, str],
                   typing.Optional[str], Tuple[int, ...],
                   typing.Callable[[str], bytes],
                   Self, LiteralString, Never]

        for t in samples:
            x = Annotated[t, "a"]

            for prot in range(pickle.HIGHEST_PROTOCOL + 1):
                with self.subTest(protocol=prot, type=t):
                    pickled = pickle.dumps(x, prot)
                    restored = pickle.loads(pickled)
                    self.assertEqual(x, restored)

        global _Annotated_test_G

        class _Annotated_test_G(Generic[T]):
            x = 1

        G = Annotated[_Annotated_test_G[int], "A decoration"]
        G.foo = 42
        G.bar = 'abc'

        for proto in range(pickle.HIGHEST_PROTOCOL + 1):
            z = pickle.dumps(G, proto)
            x = pickle.loads(z)
            self.assertEqual(x.foo, 42)
            self.assertEqual(x.bar, 'abc')
            self.assertEqual(x.x, 1)

    def test_subst(self):
        dec = "a decoration"
        dec2 = "another decoration"

        S = Annotated[T, dec2]
        self.assertEqual(S[int], Annotated[int, dec2])

        self.assertEqual(S[Annotated[int, dec]], Annotated[int, dec, dec2])
        L = Annotated[List[T], dec]

        self.assertEqual(L[int], Annotated[List[int], dec])
        with self.assertRaises(TypeError):
            L[int, int]

        self.assertEqual(S[L[int]], Annotated[List[int], dec, dec2])

        D = Annotated[Dict[KT, VT], dec]
        self.assertEqual(D[str, int], Annotated[Dict[str, int], dec])
        with self.assertRaises(TypeError):
            D[int]

        It = Annotated[int, dec]
        with self.assertRaises(TypeError):
            It[None]

        LI = L[int]
        with self.assertRaises(TypeError):
            LI[None]

    def test_annotated_in_other_types(self):
        X = List[Annotated[T, 5]]
        self.assertEqual(X[int], List[Annotated[int, 5]])


class CoolEmployee(NamedTuple):
    name: str
    cool: int


class CoolEmployeeWithDefault(NamedTuple):
    name: str
    cool: int = 0


class XMeth(NamedTuple):
    x: int

    def double(self):
        return 2 * self.x


class XRepr(NamedTuple):
    x: int
    y: int = 1

    def __str__(self):
        return f'{self.x} -> {self.y}'

    def __add__(self, other):
        return 0


if __name__ == '__main__':
    main()
