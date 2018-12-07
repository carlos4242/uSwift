//
// A bare-bones Swift standard library
// derived from https://github.com/apple/swift/blob/master/validation-test/stdlib/MicroStdlib/Inputs/Swift.swift
//
// Copied and pasted together from bits of the apple swift standard library with
// a lot of hacking and tweaking. Don't use this for your own stuff. It probably
// won't work! Apple Swift has a perfectly good standard library, this is a
// research piece and I might incorporate this or a similar thing into my
// Swift for Arduino product at some point but otherwise it's probably never
// going to "work" and it's just to help me and others understand how the
// standard library works, it's limitations and what can be done with it.
// 
// Some day, when Swift for Arduino has matured and developed into a full
// fledged company, I hope to open source the product and create a production
// ready version of this. For now it's just for interest and research. I hope
// people find it interesting!
//
// I've no idea what the copyright is, as I'm not a lawyer. :)
// 

@_transparent
public func ~= <T : Equatable>(a: T, b: T) -> Bool {
  return a == b
}

// precedencegroup AssignmentPrecedence { assignment: true }
precedencegroup AssignmentPrecedence {
  assignment: true
  associativity: right
}
precedencegroup FunctionArrowPrecedence {
  associativity: right
  higherThan: AssignmentPrecedence
}
precedencegroup TernaryPrecedence {
  associativity: right
  higherThan: FunctionArrowPrecedence
}
precedencegroup DefaultPrecedence {
  higherThan: TernaryPrecedence
}
precedencegroup LogicalDisjunctionPrecedence {
  associativity: left
  higherThan: TernaryPrecedence
}
precedencegroup LogicalConjunctionPrecedence {
  associativity: left
  higherThan: LogicalDisjunctionPrecedence
}
precedencegroup ComparisonPrecedence {
  higherThan: LogicalConjunctionPrecedence
}
precedencegroup NilCoalescingPrecedence {
  associativity: right
  higherThan: ComparisonPrecedence
}
precedencegroup CastingPrecedence {
  higherThan: NilCoalescingPrecedence
}
precedencegroup RangeFormationPrecedence {
  higherThan: CastingPrecedence
}
precedencegroup AdditionPrecedence {
  associativity: left
  higherThan: RangeFormationPrecedence
}
precedencegroup MultiplicationPrecedence {
  associativity: left
  higherThan: AdditionPrecedence
}
precedencegroup BitwiseShiftPrecedence {
  higherThan: MultiplicationPrecedence
}

infix operator  <  : ComparisonPrecedence
infix operator  <= : ComparisonPrecedence
infix operator  >  : ComparisonPrecedence
infix operator  >= : ComparisonPrecedence
infix operator  == : ComparisonPrecedence
infix operator  != : ComparisonPrecedence
infix operator === : ComparisonPrecedence
infix operator !== : ComparisonPrecedence
infix operator  ~= : ComparisonPrecedence
infix operator && : LogicalConjunctionPrecedence
infix operator || : LogicalDisjunctionPrecedence

postfix operator ++
postfix operator --
postfix operator ...

prefix operator ++
prefix operator --
prefix operator !
prefix operator ~
prefix operator +
prefix operator -
prefix operator ...
prefix operator ..<

infix operator   *= : AssignmentPrecedence
infix operator  &*= : AssignmentPrecedence
infix operator   /= : AssignmentPrecedence
infix operator   %= : AssignmentPrecedence
infix operator   += : AssignmentPrecedence
infix operator  &+= : AssignmentPrecedence
infix operator   -= : AssignmentPrecedence
infix operator  &-= : AssignmentPrecedence
infix operator  <<= : AssignmentPrecedence
infix operator &<<= : AssignmentPrecedence
infix operator  >>= : AssignmentPrecedence
infix operator &>>= : AssignmentPrecedence
infix operator   &= : AssignmentPrecedence
infix operator   ^= : AssignmentPrecedence
infix operator   |= : AssignmentPrecedence

infix operator  << : BitwiseShiftPrecedence, BinaryInteger
infix operator &<< : BitwiseShiftPrecedence, FixedWidthInteger
infix operator  >> : BitwiseShiftPrecedence, BinaryInteger
infix operator &>> : BitwiseShiftPrecedence, FixedWidthInteger

// "Multiplicative"

infix operator   * : MultiplicationPrecedence, Numeric
infix operator  &* : MultiplicationPrecedence, FixedWidthInteger
infix operator   / : MultiplicationPrecedence, BinaryInteger
// infix operator   / : MultiplicationPrecedence, BinaryInteger, FloatingPoint
infix operator   % : MultiplicationPrecedence, BinaryInteger
infix operator   & : MultiplicationPrecedence, BinaryInteger

// "Additive"

infix operator   + : AdditionPrecedence, AdditiveArithmetic
infix operator  &+ : AdditionPrecedence, FixedWidthInteger
infix operator   - : AdditionPrecedence, AdditiveArithmetic
infix operator  &- : AdditionPrecedence, FixedWidthInteger
infix operator   | : AdditionPrecedence, BinaryInteger
infix operator   ^ : AdditionPrecedence, BinaryInteger

// FIXME: is this the right precedence level for "..." ?
infix operator  ... : RangeFormationPrecedence, Comparable
infix operator  ..< : RangeFormationPrecedence, Comparable

// public typealias Void = ()
public typealias _MaxBuiltinIntegerType = Builtin.Int2048
// public typealias _MaxBuiltinFloatType = Builtin.FPIEEE64
public typealias _MaxBuiltinFloatType = Builtin.FPIEEE32

// public typealias CInt = Int32
// public typealias CChar = Int8

public typealias Void = ()
public typealias IntegerLiteralType = Int
public typealias FloatLiteralType = Float
public typealias BooleanLiteralType = Bool
// public typealias FloatLiteralType = Double

public typealias AnyObject = Builtin.AnyObject
public typealias AnyClass = AnyObject.Type

// these are necessary for the clang importer to work
public typealias CChar = Int8

public typealias CUnsignedChar = UInt8
public typealias CUnsignedShort = UInt16
public typealias CUnsignedInt = UInt32
public typealias CUnsignedLong = UInt
// public typealias CUnsignedLongLong = UInt64

public typealias CSignedChar = Int8
public typealias CShort = Int16
public typealias CInt = Int32
public typealias CLong = Int
// public typealias CLongLong = Int64
public typealias CFloat = Float
// public typealias CDouble = Double

// public typealias CLongDouble = Double
// public typealias CWideChar = Unicode.Scalar

public typealias CChar16 = UInt16
// public typealias CChar32 = Unicode.Scalar
public typealias CBool = Bool

public protocol RawRepresentable {

  associatedtype RawValue

  init?(rawValue: RawValue)

  var rawValue: RawValue { get }
}

@inlinable // FIXME(sil-serialize-all)
public func == <T : RawRepresentable>(lhs: T, rhs: T) -> Bool
  where T.RawValue : Equatable {
  return lhs.rawValue == rhs.rawValue
}

@inlinable // FIXME(sil-serialize-all)
public func != <T : RawRepresentable>(lhs: T, rhs: T) -> Bool
  where T.RawValue : Equatable {
  return lhs.rawValue != rhs.rawValue
}

@inlinable // FIXME(sil-serialize-all)
public func != <T : Equatable>(lhs: T, rhs: T) -> Bool
  where T : RawRepresentable, T.RawValue : Equatable {
  return lhs.rawValue != rhs.rawValue
}

// public protocol CaseIterable {
//   /// A type that can represent a collection of all values of this type.
//   associatedtype AllCases: Collection
//     where AllCases.Element == Self
  
//   /// A collection of all values of this type.
//   static var allCases: AllCases { get }
// }

public protocol ExpressibleByNilLiteral {
  /// Creates an instance initialized with `nil`.
  init(nilLiteral: ())
}

public protocol _ExpressibleByBuiltinIntegerLiteral {
  init(_builtinIntegerLiteral value: Builtin.IntLiteral)
}

public protocol ExpressibleByIntegerLiteral {
  associatedtype IntegerLiteralType : _ExpressibleByBuiltinIntegerLiteral
  init(integerLiteral value: IntegerLiteralType)
}

public protocol _ExpressibleByBuiltinFloatLiteral {
  init(_builtinFloatLiteral value: _MaxBuiltinFloatType)
}

public protocol ExpressibleByFloatLiteral {
  associatedtype FloatLiteralType : _ExpressibleByBuiltinFloatLiteral
  init(floatLiteral value: FloatLiteralType)
}

public protocol _ExpressibleByBuiltinBooleanLiteral {
  init(_builtinBooleanLiteral value: Builtin.Int1)
}

public protocol ExpressibleByBooleanLiteral {
  associatedtype BooleanLiteralType : _ExpressibleByBuiltinBooleanLiteral
  init(booleanLiteral value: BooleanLiteralType)
}

// @_frozen
public enum Never {}

// extension Never: Error {}

extension Never: Equatable {}

// extension Never: Comparable {
//   public static func < (lhs: Never, rhs: Never) -> Bool {
//     switch (lhs, rhs) {
//     }
//   }
// }

@_transparent
public // @testable
func _canBeClass<T>(_: T.Type) -> Int8 {
  return Int8(Builtin.canBeClass(T.self))
}

@inlinable // unsafe-performance
@_transparent
public func unsafeBitCast<T, U>(_ x: T, to type: U.Type) -> U {
  // _precondition(MemoryLayout<T>.size == MemoryLayout<U>.size,
    // "Can't unsafeBitCast between types of different sizes")
  return Builtin.reinterpretCast(x)
}

@_transparent
public func _identityCast<T, U>(_ x: T, to expectedType: U.Type) -> U {
  // _precondition(T.self == expectedType, "_identityCast to wrong type")
  return Builtin.reinterpretCast(x)
}

@usableFromInline @_transparent
internal func _reinterpretCastToAnyObject<T>(_ x: T) -> AnyObject {
  return unsafeBitCast(x, to: AnyObject.self)
}

@usableFromInline @_transparent
internal func == (
  lhs: Builtin.NativeObject, rhs: Builtin.NativeObject
) -> Bool {
  return unsafeBitCast(lhs, to: Int.self) == unsafeBitCast(rhs, to: Int.self)
}

@usableFromInline @_transparent
internal func != (
  lhs: Builtin.NativeObject, rhs: Builtin.NativeObject
) -> Bool {
  return !(lhs == rhs)
}

@usableFromInline @_transparent
internal func == (
  lhs: Builtin.RawPointer, rhs: Builtin.RawPointer
) -> Bool {
  return unsafeBitCast(lhs, to: Int.self) == unsafeBitCast(rhs, to: Int.self)
}

@usableFromInline @_transparent
internal func != (lhs: Builtin.RawPointer, rhs: Builtin.RawPointer) -> Bool {
  return !(lhs == rhs)
}

@inlinable
public func == (t0: Any.Type?, t1: Any.Type?) -> Bool {
  switch (t0, t1) {
  case (.none, .none): return true
  case let (.some(ty0), .some(ty1)):
    return Bool(Builtin.is_same_metatype(ty0, ty1))
  default: return false
  }
}

@inlinable
public func != (t0: Any.Type?, t1: Any.Type?) -> Bool {
  return !(t0 == t1)
}

@usableFromInline @_transparent
internal func _unreachable(_ condition: Bool = true) {
  if condition {
    Builtin.unreachable()
  }
}

@usableFromInline @_transparent
internal func _conditionallyUnreachable() -> Never {
  Builtin.conditionallyUnreachable()
}

@_transparent
public func _unsafeReferenceCast<T, U>(_ x: T, to: U.Type) -> U {
  return Builtin.castReference(x)
}

@_transparent
public func unsafeDowncast<T : AnyObject>(_ x: AnyObject, to type: T.Type) -> T {
  // _debugPrecondition(x is T, "invalid unsafeDowncast")
  return Builtin.castReference(x)
}

@_transparent
public func _unsafeUncheckedDowncast<T : AnyObject>(_ x: AnyObject, to type: T.Type) -> T {
  // _sanityCheck(x is T, "invalid unsafeDowncast")
  return Builtin.castReference(x)
}

// @inlinable
// internal
// func _isValidAddress(_ address: UInt) -> Bool {
//   // TODO: define (and use) ABI max valid pointer value
//   return address >= _swift_abi_LeastValidPointerValue
// }

// NEEDS OBJC
// @inlinable // FIXME(sil-serialize-all)
// internal func _unsafeDowncastToAnyObject(fromAny any: Any) -> AnyObject {
//   // _sanityCheck(type(of: any) is AnyObject.Type
//   //              || type(of: any) is AnyObject.Protocol,
//   //              "Any expected to contain object reference")
//   return any as AnyObject
// }

@inlinable // FIXME(sil-serialize-all)
@inline(__always)
public // internal with availability
func _trueAfterDiagnostics() -> Builtin.Int1 {
  let val: Bool = true
  return val._value
}

@usableFromInline @_transparent
internal func _preconditionFailure(
  // _ message: StaticString = StaticString(),
  // file: StaticString = #file, line: UInt = #line
) -> Never {
  // _precondition(false, message, file: file, line: line)
  _conditionallyUnreachable()
}

@usableFromInline @_transparent
internal func _debugPreconditionFailure(
  // _ message: StaticString = StaticString(),
  // file: StaticString = #file, line: UInt = #line
) -> Never {
  // if _slowPath(_isDebugAssertConfiguration()) {
  //   _precondition(false, message, file: file, line: line)
  // }
  _conditionallyUnreachable()
}

@usableFromInline @_transparent
internal func _sanityCheckFailure(
  // _ message: StaticString = StaticString(),
  // file: StaticString = #file, line: UInt = #line
) -> Never {
  // _sanityCheck(false, message, file: file, line: line)
  _conditionallyUnreachable()
}

@usableFromInline @_transparent
@_semantics("branchhint")
internal func _branchHint(_ actual: Bool, expected: Bool) -> Bool {
  return Bool(Builtin.int_expect_Int1(actual._value, expected._value))
}

/// Optimizer hint that `x` is expected to be `true`.
@_transparent
@_semantics("fastpath")
public func _fastPath(_ x: Bool) -> Bool {
  return _branchHint(x, expected: true)
}

/// Optimizer hint that `x` is expected to be `false`.
@_transparent
@_semantics("slowpath")
public func _slowPath(_ x: Bool) -> Bool {
  return _branchHint(x, expected: false)
}

/// Optimizer hint that the code where this function is called is on the fast
/// path.
@_transparent
public func _onFastPath() {
  Builtin.onFastPath()
}

@inlinable // FIXME(sil-serialize-all)
@inline(__always)
internal func _bitPattern(_ x: Builtin.BridgeObject) -> UInt {
  return UInt(Builtin.castBitPatternFromBridgeObject(x))
}

@inline(__always)
@inlinable
public func _bridgeObject(fromNative x: AnyObject) -> Builtin.BridgeObject {
  // _sanityCheck(!_isObjCTaggedPointer(x))
  let object = Builtin.castToBridgeObject(x, 0._builtinWordValue)
  // _sanityCheck(_isNativePointer(object))
  return object
}

// @inline(__always)
// @inlinable
// public func _bridgeObject(
//   fromNonTaggedObjC x: AnyObject
// ) -> Builtin.BridgeObject {
//   // _sanityCheck(!_isObjCTaggedPointer(x))
//   let object = _makeObjCBridgeObject(x)
//   // _sanityCheck(_isNonTaggedObjCPointer(object))
//   return object
// }

@inline(__always)
@inlinable
public func _bridgeObject(fromTagged x: UInt) -> Builtin.BridgeObject {
  // _sanityCheck(x & _objCTaggedPointerBits != 0)
  let object: Builtin.BridgeObject = Builtin.valueToBridgeObject(x._value)
  // _sanityCheck(_isTaggedObject(object))
  return object
}

// @inline(__always)
// @inlinable
// public func _bridgeObject(taggingPayload x: UInt) -> Builtin.BridgeObject {
//   let shifted = x &<< _objectPointerLowSpareBitShift
//   // _sanityCheck(x == (shifted &>> _objectPointerLowSpareBitShift),
//   //   "out-of-range: limited bit range requires some zero top bits")
//   // _sanityCheck(shifted & _objCTaggedPointerBits == 0,
//   //   "out-of-range: post-shift use of tag bits")
//   return _bridgeObject(fromTagged: shifted | _objCTaggedPointerBits)
// }

// BridgeObject -> Values
@inline(__always)
@inlinable
public func _bridgeObject(toNative x: Builtin.BridgeObject) -> AnyObject {
  // _sanityCheck(_isNativePointer(x))
  return Builtin.castReferenceFromBridgeObject(x)
}

@inline(__always)
@inlinable
public func _bridgeObject(
  toNonTaggedObjC x: Builtin.BridgeObject
) -> AnyObject {
  // _sanityCheck(_isNonTaggedObjCPointer(x))
  return Builtin.castReferenceFromBridgeObject(x)
}

@inline(__always)
@inlinable
public func _bridgeObject(toTagged x: Builtin.BridgeObject) -> UInt {
  // _sanityCheck(_isTaggedObject(x))
  let bits = _bitPattern(x)
  // _sanityCheck(bits & _objCTaggedPointerBits != 0)
  return bits
}

// @inline(__always)
// @inlinable
// public func _bridgeObject(toTagPayload x: Builtin.BridgeObject) -> UInt {
//   return _getNonTagBits(x)
// }

@inline(__always)
@inlinable
public func _bridgeObject(
  fromNativeObject x: Builtin.NativeObject
) -> Builtin.BridgeObject {
  return _bridgeObject(fromNative: _nativeObject(toNative: x))
}

@inline(__always)
@inlinable
public func _nativeObject(fromNative x: AnyObject) -> Builtin.NativeObject {
  // _sanityCheck(!_isObjCTaggedPointer(x))
  let native = Builtin.unsafeCastToNativeObject(x)
  // _sanityCheck(native == Builtin.castToNativeObject(x))
  return native
}
@inline(__always)
@inlinable
public func _nativeObject(
  fromBridge x: Builtin.BridgeObject
) -> Builtin.NativeObject {
  return _nativeObject(fromNative: _bridgeObject(toNative: x))
}

@inline(__always)
@inlinable
public func _nativeObject(toNative x: Builtin.NativeObject) -> AnyObject {
  return Builtin.castFromNativeObject(x)
}

@inlinable // FIXME(sil-serialize-all)
@inline(__always)
internal func _makeNativeBridgeObject(
  _ nativeObject: AnyObject, _ bits: UInt
) -> Builtin.BridgeObject {
  // _sanityCheck(
  //   (bits & _objectPointerIsObjCBit) == 0,
  //   "BridgeObject is treated as non-native when ObjC bit is set"
  // )
  return _makeBridgeObject(nativeObject, bits)
}

/// Create a `BridgeObject` around the given `objCObject`.
// @inlinable // FIXME(sil-serialize-all)
// @inline(__always)
// public // @testable
// func _makeObjCBridgeObject(
//   _ objCObject: AnyObject
// ) -> Builtin.BridgeObject {
//   return _makeBridgeObject(
//     objCObject,
//     _isObjCTaggedPointer(objCObject) ? 0 : _objectPointerIsObjCBit)
// }

/// Create a `BridgeObject` around the given `object` with the
/// given spare bits.
///
/// - Precondition:
///
///   1. `bits & _objectPointerSpareBits == bits`
///   2. if `object` is a tagged pointer, `bits == 0`.  Otherwise,
///      `object` is either a native object, or `bits ==
///      _objectPointerIsObjCBit`.
@inlinable // FIXME(sil-serialize-all)
@inline(__always)
internal func _makeBridgeObject(
  _ object: AnyObject, _ bits: UInt
) -> Builtin.BridgeObject {
  // _sanityCheck(!_isObjCTaggedPointer(object) || bits == 0,
  //   "Tagged pointers cannot be combined with bits")

  // _sanityCheck(
  //   _isObjCTaggedPointer(object)
  //   || _usesNativeSwiftReferenceCounting(type(of: object))
  //   || bits == _objectPointerIsObjCBit,
  //   "All spare bits must be set in non-native, non-tagged bridge objects"
  // )

  // _sanityCheck(
  //   bits & _objectPointerSpareBits == bits,
  //   "Can't store non-spare bits into Builtin.BridgeObject")

  return Builtin.castToBridgeObject(
    object, bits._builtinWordValue
  )
}

@usableFromInline @_transparent
internal func _isUnique<T>(_ object: inout T) -> Bool {
  return Bool(Builtin.isUnique(&object))
}

@_transparent
public // @testable
func _isUnique_native<T>(_ object: inout T) -> Bool {
  // This could be a bridge object, single payload enum, or plain old
  // reference. Any case it's non pointer bits must be zero, so
  // force cast it to BridgeObject and check the spare bits.
  // _sanityCheck(
  //   (_bitPattern(Builtin.reinterpretCast(object)) & _objectPointerSpareBits)
  //   == 0)
  // _sanityCheck(_usesNativeSwiftReferenceCounting(
  //     type(of: Builtin.reinterpretCast(object) as AnyObject)))
  return Bool(Builtin.isUnique_native(&object))
}

/// Returns `true` if type is a POD type. A POD type is a type that does not
/// require any special handling on copying or destruction.
@_transparent
public // @testable
func _isPOD<T>(_ type: T.Type) -> Bool {
  return Bool(Builtin.ispod(type))
}

/// Returns `true` if type is a bitwise takable. A bitwise takable type can
/// just be moved to a different address in memory.
@_transparent
public // @testable
func _isBitwiseTakable<T>(_ type: T.Type) -> Bool {
  return Bool(Builtin.isbitwisetakable(type))
}

/// Returns `true` if type is nominally an Optional type.
@_transparent
public // @testable
func _isOptional<T>(_ type: T.Type) -> Bool {
  return Bool(Builtin.isOptional(type))
}

@_frozen
public enum Optional<Wrapped> : ExpressibleByNilLiteral {
  case none
  case some(Wrapped)

  @_transparent
  public init(_ some: Wrapped) { self = .some(some) }

  @inlinable
  public func map<U>(
    _ transform: (Wrapped) throws -> U
  ) rethrows -> U? {
    switch self {
    case .some(let y):
      return .some(try transform(y))
    case .none:
      return .none
    }
  }

  @inlinable
  public func flatMap<U>(
    _ transform: (Wrapped) throws -> U?
  ) rethrows -> U? {
    switch self {
    case .some(let y):
      return try transform(y)
    case .none:
      return .none
    }
  }

  @_transparent
  public init(nilLiteral: ()) {
    self = .none
  }

  @inlinable
  public var unsafelyUnwrapped: Wrapped {
    @inline(__always)
    get {
      if let x = self {
        return x
      }
      _debugPreconditionFailure()
    }
  }

  @inlinable
  internal var _unsafelyUnwrappedUnchecked: Wrapped {
    @inline(__always)
    get {
      if let x = self {
        return x
      }
      _sanityCheckFailure()//"_unsafelyUnwrappedUnchecked of nil optional")
    }
  }
}

@_transparent
public // COMPILER_INTRINSIC
func _diagnoseUnexpectedNilOptional(_filenameStart: Builtin.RawPointer,
                                    _filenameLength: Builtin.Word,
                                    _filenameIsASCII: Builtin.Int1,
                                    _line: Builtin.Word,
                                    _isImplicitUnwrap: Builtin.Int1) {
  _preconditionFailure()
    // Bool(_isImplicitUnwrap)
    //   ? "Unexpectedly found nil while implicitly unwrapping an Optional value"
    //   : "Unexpectedly found nil while unwrapping an Optional value",
    // file: StaticString(_start: _filenameStart,
    //                    utf8CodeUnitCount: _filenameLength,
    //                    isASCII: _filenameIsASCII),
    // line: UInt(_line))
}

@_transparent
@_semantics("typechecker.type(of:)")
public func type<T, Metatype>(of value: T) -> Metatype {
  // This implementation is never used, since calls to `Swift.type(of:)` are
  // resolved as a special case by the type checker.
  // Builtin.staticReport(_trueAfterDiagnostics(), true._value,
  //   ("internal consistency error: 'type(of:)' operation failed to resolve"
  //    as StaticString).utf8Start._rawValue)
  Builtin.unreachable()
}

extension Optional : Equatable where Wrapped : Equatable {
  @inlinable
  public static func ==(lhs: Wrapped?, rhs: Wrapped?) -> Bool {
    switch (lhs, rhs) {
    case let (l?, r?):
      return l == r
    case (nil, nil):
      return true
    default:
      return false
    }
  }

  @inlinable
  public static func !=(lhs: Wrapped?, rhs: Wrapped?) -> Bool {
    return !(lhs == rhs)
  }
}

@_fixed_layout
public struct _OptionalNilComparisonType : ExpressibleByNilLiteral {
  /// Create an instance initialized with `nil`.
  @_transparent
  public init(nilLiteral: ()) {
  }
}

extension Optional {
  @_transparent
  public static func ~=(lhs: _OptionalNilComparisonType, rhs: Wrapped?) -> Bool {
    switch rhs {
    case .some:
      return false
    case .none:
      return true
    }
  }

  @_transparent
  public static func ==(lhs: Wrapped?, rhs: _OptionalNilComparisonType) -> Bool {
    switch lhs {
    case .some:
      return false
    case .none:
      return true
    }
  }

  @_transparent
  public static func !=(lhs: Wrapped?, rhs: _OptionalNilComparisonType) -> Bool {
    switch lhs {
    case .some:
      return true
    case .none:
      return false
    }
  }

  @_transparent
  public static func ==(lhs: _OptionalNilComparisonType, rhs: Wrapped?) -> Bool {
    switch rhs {
    case .some:
      return false
    case .none:
      return true
    }
  }

  @_transparent
  public static func !=(lhs: _OptionalNilComparisonType, rhs: Wrapped?) -> Bool {
    switch rhs {
    case .some:
      return true
    case .none:
      return false
    }
  }
}

// #if _runtime(_ObjC)

// @inlinable
// @_silgen_name("_swift_isClassOrObjCExistentialType")
// internal func _swift_isClassOrObjCExistentialType<T>(_ x: T.Type) -> Bool

// @inlinable
// @inline(__always)
// internal func _isClassOrObjCExistential<T>(_ x: T.Type) -> Bool {

//   let cbc = _canBeClass(x)
//   // let zero: Int8 = 0
//   // let one: Int8 = 1

//   if cbc == 0 {
//     return false
//   } else if cbc == 1 {
//     return true
//   } else {
//     return _swift_isClassOrObjCExistentialType(x)
//   }

//   // should be this but life is too short...
//   // switch _canBeClass(x) {
//   // // Is not a class.
//   // case 0:
//   //   return false
//   // // Is a class.
//   // case 1:
//   //   return true
//   // // Maybe a class.
//   // default:
//   //   return _swift_isClassOrObjCExistentialType(x)
//   // }
// }

// @inlinable // FIXME(sil-serialize-all)
// public func _bridgeAnythingToObjectiveC<T>(_ x: T) -> AnyObject {
//   if _fastPath(_isClassOrObjCExistential(T.self)) {
//     return unsafeBitCast(x, to: AnyObject.self)
//   }
//   return _bridgeAnythingNonVerbatimToObjectiveC(x)
// }

// @_silgen_name("")
// public func _bridgeAnythingNonVerbatimToObjectiveC<T>(_ x: __owned T) -> AnyObject

// /// Convert a purportedly-nonnull `id` value from Objective-C into an Any.
// ///
// /// Since Objective-C APIs sometimes get their nullability annotations wrong,
// /// this includes a failsafe against nil `AnyObject`s, wrapping them up as
// /// a nil `AnyObject?`-inside-an-`Any`.
// ///
// /// COMPILER_INTRINSIC
// @inlinable // FIXME(sil-serialize-all)
// public func _bridgeAnyObjectToAny(_ possiblyNullObject: AnyObject?) -> Any {
//   if let nonnullObject = possiblyNullObject {
//     return nonnullObject // AnyObject-in-Any
//   }
//   return possiblyNullObject as Any
// }

// public protocol _ObjectiveCBridgeable {
//   associatedtype _ObjectiveCType : AnyObject

//   /// Convert `self` to Objective-C.
//   func _bridgeToObjectiveC() -> _ObjectiveCType

//   static func _forceBridgeFromObjectiveC(
//     _ source: _ObjectiveCType,
//     result: inout Self?
//   )

//   @discardableResult
//   static func _conditionallyBridgeFromObjectiveC(
//     _ source: _ObjectiveCType,
//     result: inout Self?
//   ) -> Bool

//   static func _unconditionallyBridgeFromObjectiveC(_ source: _ObjectiveCType?)
//       -> Self
// }

// extension Optional : _ObjectiveCBridgeable {
//   // The object that represents `none` for an Optional of this type.
//   @inlinable // FIXME(sil-serialize-all)
//   internal static var _nilSentinel : AnyObject {
//     @_silgen_name("_swift_Foundation_getOptionalNilSentinelObject")
//     get
//   }

//   @inlinable // FIXME(sil-serialize-all)
//   public func _bridgeToObjectiveC() -> AnyObject {
//     // Bridge a wrapped value by unwrapping.
//     if let value = self {
//       return _bridgeAnythingToObjectiveC(value)
//     }
//     // Bridge nil using a sentinel.
//     let typeVar = type(of: self)
//     return typeVar._nilSentinel
//   }

//   @inlinable // FIXME(sil-serialize-all)
//   public static func _forceBridgeFromObjectiveC(
//     _ source: AnyObject,
//     result: inout Optional<Wrapped>?
//   ) {
//     // Map the nil sentinel back to .none.
//     // NB that the signature of _forceBridgeFromObjectiveC adds another level
//     // of optionality, so we need to wrap the immediate result of the conversion
//     // in `.some`.
//     if source === _nilSentinel {
//       result = .some(.none)
//       return
//     }
//     // Otherwise, force-bridge the underlying value.
//     let unwrappedResult = source as! Wrapped
//     result = .some(.some(unwrappedResult))
//   }

//   @inlinable // FIXME(sil-serialize-all)
//   public static func _conditionallyBridgeFromObjectiveC(
//     _ source: AnyObject,
//     result: inout Optional<Wrapped>?
//   ) -> Bool {
//     // Map the nil sentinel back to .none.
//     // NB that the signature of _forceBridgeFromObjectiveC adds another level
//     // of optionality, so we need to wrap the immediate result of the conversion
//     // in `.some` to indicate success of the bridging operation, with a nil
//     // result.
//     if source === _nilSentinel {
//       result = .some(.none)
//       return true
//     }
//     // Otherwise, try to bridge the underlying value.
//     if let unwrappedResult = source as? Wrapped {
//       result = .some(.some(unwrappedResult))
//       return true
//     } else {
//       result = .none
//       return false
//     }
//   }

//   @inlinable // FIXME(sil-serialize-all)
//   public static func _unconditionallyBridgeFromObjectiveC(_ source: AnyObject?)
//       -> Optional<Wrapped> {
//     if let nonnullSource = source {
//       // Map the nil sentinel back to none.
//       if nonnullSource === _nilSentinel {
//         return .none
//       } else {
//         return .some(nonnullSource as! Wrapped)
//       }
//     } else {
//       // If we unexpectedly got nil, just map it to `none` too.
//       return .none
//     }
//   }
// }
// #endif

// public protocol Strideable : Comparable {
//   associatedtype Stride : SignedNumeric, Comparable
//   func distance(to other: Self) -> Stride
//   func advanced(by n: Stride) -> Self
//   static func _step(
//     after current: (index: Int?, value: Self),
//     from start: Self, by distance: Self.Stride
//   ) -> (index: Int?, value: Self)
// }

extension ExpressibleByIntegerLiteral
  where Self : _ExpressibleByBuiltinIntegerLiteral {
  @_transparent
  public init(integerLiteral value: Self) {
    self = value
  }
}

// public protocol SignedNumeric : Numeric {
//   static prefix func - (_ operand: Self) -> Self
//   mutating func negate()
// }

public protocol AdditiveArithmetic : Equatable {
  // static var zero: Self { get }
  // static func +(lhs: Self, rhs: Self) -> Self
  // static func +=(lhs: inout Self, rhs: Self)
  // static func -(lhs: Self, rhs: Self) -> Self
  // static func -=(lhs: inout Self, rhs: Self)
}

public protocol Numeric : AdditiveArithmetic, Comparable, ExpressibleByIntegerLiteral {
}

public protocol BinaryInteger : Numeric
 // :
 //  Hashable, , CustomStringConvertible, Strideable
 //  where Magnitude : BinaryInteger, Magnitude.Magnitude == Magnitude
{
  // init<T : BinaryFloatingPoint>(_ source: T)

  init<T : BinaryInteger>(_ source: T)
  init<T : BinaryInteger>(truncatingIfNeeded source: T)
  static var isSigned: Bool { get }
  var bitWidth: Int { get }

  // init<T : BinaryInteger>(clamping source: T)
  // var bitWidth: Int { get }
  // static func /(lhs: Self, rhs: Self) -> Self
  // static func /=(lhs: inout Self, rhs: Self)
  // static func %(lhs: Self, rhs: Self) -> Self
  // static func %=(lhs: inout Self, rhs: Self)
  // override static func +(lhs: Self, rhs: Self) -> Self
  // override static func +=(lhs: inout Self, rhs: Self)
  // override static func -(lhs: Self, rhs: Self) -> Self
  // override static func -=(lhs: inout Self, rhs: Self)
  // override static func *(lhs: Self, rhs: Self) -> Self
  // override static func *=(lhs: inout Self, rhs: Self)
  // static prefix func ~ (_ x: Self) -> Self
  // static func &(lhs: Self, rhs: Self) -> Self
  // static func &=(lhs: inout Self, rhs: Self)
  // static func |(lhs: Self, rhs: Self) -> Self
  // static func |=(lhs: inout Self, rhs: Self)
  // static func ^(lhs: Self, rhs: Self) -> Self
  // static func ^=(lhs: inout Self, rhs: Self)
  // static func >> <RHS: BinaryInteger>(lhs: Self, rhs: RHS) -> Self
  // static func >>= <RHS: BinaryInteger>(lhs: inout Self, rhs: RHS)
  // static func << <RHS: BinaryInteger>(lhs: Self, rhs: RHS) -> Self
  // static func <<=<RHS: BinaryInteger>(lhs: inout Self, rhs: RHS)
}

extension BinaryInteger {
  /// Creates a new value equal to zero.
  // @_transparent
  // public init() {
  //   self = 0
  // }

  @inlinable // FIXME(sil-serialize-all)
  @inline(__always)
  public static func == <
    Other : BinaryInteger
  >(lhs: Self, rhs: Other) -> Bool {
    let lhsNegative = Self.isSigned && lhs < (0 as Self)
    let rhsNegative = Other.isSigned && rhs < (0 as Other)

    if lhsNegative != rhsNegative { return false }

    // Here we know the values are of the same sign.
    //
    // There are a few possible scenarios from here:
    //
    // 1. Both values are negative
    //  - If one value is strictly wider than the other, then it is safe to
    //    convert to the wider type.
    //  - If the values are of the same width, it does not matter which type we
    //    choose to convert to as the values are already negative, and thus
    //    include the sign bit if two's complement representation already.
    // 2. Both values are non-negative
    //  - If one value is strictly wider than the other, then it is safe to
    //    convert to the wider type.
    //  - If the values are of the same width, than signedness matters, as not
    //    unsigned types are 'wider' in a sense they don't need to 'waste' the
    //    sign bit. Therefore it is safe to convert to the unsigned type.

    if lhs.bitWidth < rhs.bitWidth {
      return Other(truncatingIfNeeded: lhs) == rhs
    }
    if lhs.bitWidth > rhs.bitWidth {
      return lhs == Self(truncatingIfNeeded: rhs)
    }

    if Self.isSigned {
      return Other(truncatingIfNeeded: lhs) == rhs
    }
    return lhs == Self(truncatingIfNeeded: rhs)
  }

  @_transparent
  public static func != <
    Other : BinaryInteger
  >(lhs: Self, rhs: Other) -> Bool {
    return !(lhs == rhs)
  }
}

public protocol FixedWidthInteger : BinaryInteger
//  , LosslessStringConvertible
// where Magnitude : FixedWidthInteger & UnsignedInteger,
//       Stride : FixedWidthInteger & SignedInteger
{
  static var bitWidth: Int { get }
  // static var max: Self { get }
  // static var min: Self { get }

  init(_truncatingBits bits: UInt)

  // var nonzeroBitCount: Int { get }
  // var leadingZeroBitCount: Int { get }
     // func addingReportingOverflow(
     //   _ rhs: Self
     // ) -> (partialValue: Self, overflow: Bool)
}

extension FixedWidthInteger {
  @inlinable
  public var bitWidth: Int { return Self.bitWidth }

// original implementation is way too heavyweight...
  //   @_transparent
  // public var _lowWord: UInt {
  //   var it = words.makeIterator()
  //   return it.next() ?? 0
  // }

  @inlinable // FIXME(sil-serialize-all)
  @inline(__always)
  public init<T : BinaryInteger>(truncatingIfNeeded source: T) {
    // if Self.bitWidth == 8, T.bitWidth == 8 {
    //   self = Self(bitPattern: source)
    //   return
    // }

      // not implemented
      self = 0


    // if Self.bitWidth <= Int.bitWidth {
    //   self = Self(_truncatingBits: source._lowWord)
    // }
    // else {

    //   // let neg = source < (0 as T)
    //   // var result: Self = neg ? ~0 : 0
    //   // var shift: Self = 0
    //   // let width = Self(_truncatingBits: Self.bitWidth._lowWord)
    //   // for word in source.words {
    //   //   guard shift < width else { break }
    //   //   // Masking shift is OK here because we have already ensured
    //   //   // that shift < Self.bitWidth. Not masking results in
    //   //   // infinite recursion.
    //   //   result ^= Self(_truncatingBits: neg ? ~word : word) &<< shift
    //   //   shift += Self(_truncatingBits: Int.bitWidth._lowWord)
    //   // }
    //   // self = result
    // }
  }
}

// extension FixedWidthInteger {
//   @_transparent
//   public static func &+ (lhs: Self, rhs: Self) -> Self {
//     return lhs.addingReportingOverflow(rhs).partialValue
//   }

//   @_transparent
//   public static func &+= (lhs: inout Self, rhs: Self) {
//     lhs = lhs &+ rhs
//   }

//   @_transparent
//   public static func &- (lhs: Self, rhs: Self) -> Self {
//     return lhs.subtractingReportingOverflow(rhs).partialValue
//   }

//   @_transparent
//   public static func &-= (lhs: inout Self, rhs: Self) {
//     lhs = lhs &- rhs
//   }

//   @_transparent
//   public static func &* (lhs: Self, rhs: Self) -> Self {
//     return lhs.multipliedReportingOverflow(by: rhs).partialValue
//   }

//   @_transparent
//   public static func &*= (lhs: inout Self, rhs: Self) {
//     lhs = lhs &* rhs
//   }
// }

public protocol SignedInteger : BinaryInteger  {}
//, SignedNumeric {}

public protocol UnsignedInteger : BinaryInteger {}

extension UnsignedInteger where Self : FixedWidthInteger {
  @inlinable // FIXME(sil-serialize-all)
  @_semantics("optimize.sil.specialize.generic.partial.never")
  @inline(__always)
  public init<T : BinaryInteger>(_ source: T) {
    self.init(truncatingIfNeeded: source)
  }

  @_transparent
  public static var isSigned: Bool { return false }
}

extension SignedInteger where Self : FixedWidthInteger {
  @inlinable // FIXME(sil-serialize-all)
  @_semantics("optimize.sil.specialize.generic.partial.never")
  @inline(__always)
  public init<T : BinaryInteger>(_ source: T) {
    self.init(truncatingIfNeeded: source)
  }

  @_transparent
  public static var isSigned: Bool { return true }
}

// this version of uSwift is currently hard coded with AVR in mind, meaning 16 bit words
// Builtin.Word should be 16 bit

@_fixed_layout
public struct Int :
_ExpressibleByBuiltinIntegerLiteral, ExpressibleByIntegerLiteral,
FixedWidthInteger, SignedInteger
{
  @usableFromInline
  var _value: Builtin.Int16

  @_transparent
  public init(_builtinIntegerLiteral value: Builtin.IntLiteral) {
    self._value = Builtin.s_to_s_checked_trunc_IntLiteral_Int16(value).0
  }

  @_transparent
  public init(bitPattern x: UInt) {
    _value = x._value
  }

  @_transparent
  public init(_truncatingBits bits: UInt) {
    self.init(bitPattern: bits)
  }

  @_transparent
  public static func == (lhs: Int, rhs: Int) -> Bool {
    return Bool(Builtin.cmp_eq_Int16(lhs._value, rhs._value))
  }

  @_transparent
  public static func < (lhs: Int, rhs: Int) -> Bool {
    return Bool(Builtin.cmp_slt_Int16(lhs._value, rhs._value))
  }

  @_transparent
  public static var bitWidth : Int { return 16 }

static func +(lhs: Int, rhs: Int) -> Int {
  return lhs
}

  //   return Int(
  //     Int(
  //       Builtin.int_ctlz_Word(self._value, Bool(false)._value)
  //     )._lowWord._value)
  // }

  // @_transparent
  // public var trailingZeroBitCount: Int {
  //   return Int(
  //     Int(
  //       Builtin.int_cttz_Word(self._value, Bool(false)._value)
  //     )._lowWord._value)
  // }

  // @_transparent
  // public var nonzeroBitCount: Int {
  //   return Int(
  //     ${Self}(
  //       Builtin.int_ctpop_Int${bits}(self._value)
  //     )._lowWord._value)
  // }

  @_transparent
  public // @testable
  init(_ _v: Builtin.Word) {
    self._value = Builtin.truncOrBitCast_Word_Int16(_v)
  }

  @_transparent
  public // @testable
  var _builtinWordValue: Builtin.Word {
    return Builtin.zextOrBitCast_Int16_Word(_value)
  }
}

@_fixed_layout
public struct UInt : _ExpressibleByBuiltinIntegerLiteral, ExpressibleByIntegerLiteral,
FixedWidthInteger, UnsignedInteger
{
  @usableFromInline
  var _value: Builtin.Int16

  @_transparent
  public init(_builtinIntegerLiteral value: Builtin.IntLiteral) {
    self._value = Builtin.s_to_u_checked_trunc_IntLiteral_Int16(value).0
  }

  @_transparent
  public init(bitPattern x: Int) {
    _value = x._value
  }

  @_transparent
  public static func == (lhs: UInt, rhs: UInt) -> Bool {
    return Bool(Builtin.cmp_eq_Int16(lhs._value, rhs._value))
  }

  @_transparent
  public static func < (lhs: UInt, rhs: UInt) -> Bool {
    return Bool(Builtin.cmp_ult_Int16(lhs._value, rhs._value))
  }

  @_transparent
  public // @testable
  init(_ _v: Builtin.Word) {
    self._value = Builtin.truncOrBitCast_Word_Int16(_v)
  }

  @_transparent
  public // @testable
  var _builtinWordValue: Builtin.Word {
    return Builtin.zextOrBitCast_Int16_Word(_value)
  }

  @_transparent
  public init(_truncatingBits bits: UInt) {
    self = bits
  }

  @_transparent
  public static var bitWidth : Int { return 16 }
}

  // @_transparent
  // public // transparent
  // init(_truncatingBits bits: UInt) {
  //   // % truncOrExt = 'zext' if bits > word_bits else 'trunc'
  //   // self.init(
  //   //   Builtin.${truncOrExt}OrBitCast_Int${word_bits}_Int${bits}(bits._value))
  //   self.init(
  //     Builtin.truncOrBitCast_Int16_Int16(bits._value))
  // }


@_fixed_layout
public struct Int32 : _ExpressibleByBuiltinIntegerLiteral, ExpressibleByIntegerLiteral,
FixedWidthInteger, SignedInteger
{
  @usableFromInline
  var _value: Builtin.Int32

  @_transparent
  public init(_builtinIntegerLiteral value: Builtin.IntLiteral) {
    let builtinValue = Builtin.s_to_s_checked_trunc_IntLiteral_Int32(value).0
    self._value = builtinValue
  }

  @_transparent
  public init(bitPattern x: UInt32) {
    _value = x._value
  }

  @_transparent
  public init(_ _value: Builtin.Int32) {
    self._value = _value
  }

  @_transparent
  public static func == (lhs: Int32, rhs: Int32) -> Bool {
    return Bool(Builtin.cmp_eq_Int32(lhs._value, rhs._value))
  }

  @_transparent
  public static func < (lhs: Int32, rhs: Int32) -> Bool {
    return Bool(Builtin.cmp_slt_Int32(lhs._value, rhs._value))
  }

  @_transparent
  public init(_truncatingBits bits: UInt) {
    // this seems wrong for 16 bit words but I suspect may be hard to fix
    self.init(Builtin.zextOrBitCast_Int16_Int32(bits._value))
  }

  @_transparent
  public static var bitWidth : Int { return 32 }
}

@_fixed_layout
public struct UInt32 : _ExpressibleByBuiltinIntegerLiteral, ExpressibleByIntegerLiteral,
FixedWidthInteger, UnsignedInteger
{
  @usableFromInline
  var _value: Builtin.Int32

  @_transparent
  public init(_builtinIntegerLiteral value: Builtin.IntLiteral) {
    self._value = Builtin.s_to_u_checked_trunc_IntLiteral_Int32(value).0
  }

  @_transparent
  public init(bitPattern x: Int32) {
    _value = x._value
  }

  @_transparent
  public init(_ _value: Builtin.Int32) {
    self._value = _value
  }

  @_transparent
  public static func == (lhs: UInt32, rhs: UInt32) -> Bool {
    return Bool(Builtin.cmp_eq_Int32(lhs._value, rhs._value))
  }

  @_transparent
  public static func < (lhs: UInt32, rhs: UInt32) -> Bool {
    return Bool(Builtin.cmp_ult_Int32(lhs._value, rhs._value))
  }

  @_transparent
  public init(_truncatingBits bits: UInt) {
    // this seems wrong for 16 bit words but I suspect may be hard to fix
    self.init(Builtin.zextOrBitCast_Int16_Int32(bits._value))
  }

  @_transparent
  public static var bitWidth : Int { return 32 }
}

@_fixed_layout
public struct Int16 : _ExpressibleByBuiltinIntegerLiteral, ExpressibleByIntegerLiteral,
FixedWidthInteger, SignedInteger
{
  @usableFromInline
  var _value: Builtin.Int16

  @_transparent
  public init(_builtinIntegerLiteral value: Builtin.IntLiteral) {
    let builtinValue = Builtin.s_to_s_checked_trunc_IntLiteral_Int16(value).0
    self._value = builtinValue
  }

  @_transparent
  public init(bitPattern x: UInt16) {
    _value = x._value
  }

  @_transparent
  public init(_ _value: Builtin.Int16) {
    self._value = _value
  }

  @_transparent
  public static func == (lhs: Int16, rhs: Int16) -> Bool {
    return Bool(Builtin.cmp_eq_Int16(lhs._value, rhs._value))
  }

  @_transparent
  public static func < (lhs: Int16, rhs: Int16) -> Bool {
    return Bool(Builtin.cmp_slt_Int16(lhs._value, rhs._value))
  }

  @_transparent
  public // transparent
  init(_truncatingBits bits: UInt) {
    self.init(bits._value)
  }

  @_transparent
  public static var bitWidth : Int { return 16 }
}

@_fixed_layout
public struct UInt16 : _ExpressibleByBuiltinIntegerLiteral, ExpressibleByIntegerLiteral,
FixedWidthInteger, UnsignedInteger
{
  @usableFromInline
  var _value: Builtin.Int16

  @_transparent
  public init(_builtinIntegerLiteral value: Builtin.IntLiteral) {
    self._value = Builtin.s_to_u_checked_trunc_IntLiteral_Int16(value).0
  }

  @_transparent
  public init(bitPattern x: Int16) {
    _value = x._value
  }

  @_transparent
  public init(_ _value: Builtin.Int16) {
    self._value = _value
  }

  @_transparent
  public static func == (lhs: UInt16, rhs: UInt16) -> Bool {
    return Bool(Builtin.cmp_eq_Int16(lhs._value, rhs._value))
  }

  @_transparent
  public static func < (lhs: UInt16, rhs: UInt16) -> Bool {
    return Bool(Builtin.cmp_ult_Int16(lhs._value, rhs._value))
  }

  @_transparent
  public // transparent
  init(_truncatingBits bits: UInt) {
    self.init(bits._value)
  }

  @_transparent
  public static var bitWidth : Int { return 16 }
}

@_fixed_layout
public struct Int8 : _ExpressibleByBuiltinIntegerLiteral, ExpressibleByIntegerLiteral,
FixedWidthInteger, SignedInteger
{
  @usableFromInline
  var _value: Builtin.Int8

  @_transparent
  public init(_builtinIntegerLiteral value: Builtin.IntLiteral) {
    let builtinValue = Builtin.s_to_s_checked_trunc_IntLiteral_Int8(value).0
    self._value = builtinValue
  }

  @_transparent
  public init(bitPattern x: UInt8) {
    _value = x._value
  }

  @_transparent
  public init(_ _value: Builtin.Int8) {
    self._value = _value
  }

  @_transparent
  public static func == (lhs: Int8, rhs: Int8) -> Bool {
    return Bool(Builtin.cmp_eq_Int8(lhs._value, rhs._value))
  }

  @_transparent
  public static func < (lhs: Int8, rhs: Int8) -> Bool {
    return Bool(Builtin.cmp_slt_Int8(lhs._value, rhs._value))
  }

  @_transparent
  public init(_truncatingBits bits: UInt) {
    self.init(Builtin.truncOrBitCast_Int16_Int8(bits._value))
  }

  @_transparent
  public static var bitWidth : Int { return 8 }
}

@_fixed_layout
public struct UInt8 : _ExpressibleByBuiltinIntegerLiteral, ExpressibleByIntegerLiteral,
FixedWidthInteger, UnsignedInteger
{
  @usableFromInline
  var _value: Builtin.Int8

  @_transparent
  public init(_builtinIntegerLiteral value: Builtin.IntLiteral) {
    let builtinValue = Builtin.s_to_u_checked_trunc_IntLiteral_Int8(value).0
    self._value = builtinValue
  }

  @_transparent
  public init(bitPattern x: Int8) {
    _value = x._value
  }

  @_transparent
  public init(_ _value: Builtin.Int8) {
    self._value = _value
  }

  @_transparent
  public static func == (lhs: UInt8, rhs: UInt8) -> Bool {
    return Bool(Builtin.cmp_eq_Int8(lhs._value, rhs._value))
  }

  @_transparent
  public static func < (lhs: UInt8, rhs: UInt8) -> Bool {
    return Bool(Builtin.cmp_ult_Int8(lhs._value, rhs._value))
  }

  @_transparent
  public init(_truncatingBits bits: UInt) {
    self.init(Builtin.truncOrBitCast_Int16_Int8(bits._value))
  }

  @_transparent
  public static var bitWidth : Int { return 8 }
}

@_fixed_layout
public struct Bool {
  @usableFromInline
  internal var _value: Builtin.Int1

  @_transparent
  public init() {
    let zero: Int8 = 0
    self._value = Builtin.trunc_Int8_Int1(zero._value)
  }

  @usableFromInline @_transparent
  internal init(_ v: Builtin.Int1) { self._value = v }
  
  @inlinable
  public init(_ value: Bool) {
    self = value
  }
}

extension Bool : _ExpressibleByBuiltinBooleanLiteral, ExpressibleByBooleanLiteral {
  @_transparent
  public init(_builtinBooleanLiteral value: Builtin.Int1) {
    self._value = value
  }

  @_transparent
  public init(booleanLiteral value: Bool) {
    self = value
  }
}

extension Bool {
  // This is a magic entry point known to the compiler.
  @_transparent
  public // COMPILER_INTRINSIC
  func _getBuiltinLogicValue() -> Builtin.Int1 {
    return _value
  }
}

@_transparent
public // COMPILER_INTRINSIC
func _getBool(_ v: Builtin.Int1) -> Bool { return Bool(v) }

extension Bool: Equatable {
  @_transparent
  public static func == (lhs: Bool, rhs: Bool) -> Bool {
    return Bool(Builtin.cmp_eq_Int1(lhs._value, rhs._value))
  }
}

extension Bool {
  @_transparent
  public static prefix func ! (a: Bool) -> Bool {
    return Bool(Builtin.xor_Int1(a._value, Bool(true)._value))
  }
}


extension Bool {
  @_transparent
  @inline(__always)
  public static func && (lhs: Bool, rhs: @autoclosure () throws -> Bool) rethrows
      -> Bool {
    return lhs ? try rhs() : false
  }

  @_transparent
  @inline(__always)
  public static func || (lhs: Bool, rhs: @autoclosure () throws -> Bool) rethrows
      -> Bool {
    return lhs ? true : try rhs()
  }
}

extension Bool {
  @inlinable
  public mutating func toggle() {
    self = !self
  }
}

public protocol BinaryFloatingPoint: ExpressibleByFloatLiteral {
}

@_fixed_layout
public struct Float {
  public // @testable
  var _value: Builtin.FPIEEE32

  @_transparent
  public init() {
    let zero: Int32 = 0
    self._value = Builtin.sitofp_Int32_FPIEEE32(zero._value)
  }

  @_transparent
  public // @testable
  init(_ _value: Builtin.FPIEEE32) {
    self._value = _value
  }
}

extension Float : _ExpressibleByBuiltinFloatLiteral, BinaryFloatingPoint {
  @_transparent
  public
  init(_builtinFloatLiteral value: Builtin.FPIEEE32) {
    self = Float(value)
  }

  @_transparent
  public func isEqual(to other: Float) -> Bool {
    return Bool(Builtin.fcmp_oeq_FPIEEE32(self._value, other._value))
  }

  @_transparent
  public func isLess(than other: Float) -> Bool {
    return Bool(Builtin.fcmp_olt_FPIEEE32(self._value, other._value))
  }

  @_transparent
  public func isLessThanOrEqualTo(_ other: Float) -> Bool {
    return Bool(Builtin.fcmp_ole_FPIEEE32(self._value, other._value))
  }

  @_transparent
  public mutating func formTruncatingRemainder(dividingBy other: Float) {
    _value = Builtin.frem_FPIEEE32(self._value, other._value)
  }

  @_transparent
  public mutating func negate() {
    _value = Builtin.fneg_FPIEEE32(self._value)
  }

  @_transparent
  public static func +=(lhs: inout Float, rhs: Float) {
    lhs._value = Builtin.fadd_FPIEEE32(lhs._value, rhs._value)
  }

  @_transparent
  public static func -=(lhs: inout Float, rhs: Float) {
    lhs._value = Builtin.fsub_FPIEEE32(lhs._value, rhs._value)
  }

  @_transparent
  public static func *=(lhs: inout Float, rhs: Float) {
    lhs._value = Builtin.fmul_FPIEEE32(lhs._value, rhs._value)
  }

  @_transparent
  public static func /=(lhs: inout Float, rhs: Float) {
    lhs._value = Builtin.fdiv_FPIEEE32(lhs._value, rhs._value)
  }

  @_transparent
  public init(floatLiteral value: Float) {
    self = value
  }
}



@_fixed_layout
public struct OpaquePointer {
  @usableFromInline
  internal var _rawValue: Builtin.RawPointer

  @usableFromInline @_transparent
  internal init(_ v: Builtin.RawPointer) {
    self._rawValue = v
  }

  /// Creates an `OpaquePointer` from a given address in memory.
  @_transparent
  public init?(bitPattern: Int) {
    if bitPattern == 0 { return nil }
    self._rawValue = Builtin.inttoptr_Word(bitPattern._builtinWordValue)
  }

  /// Creates an `OpaquePointer` from a given address in memory.
  @_transparent
  public init?(bitPattern: UInt) {
    if bitPattern == 0 { return nil }
    self._rawValue = Builtin.inttoptr_Word(bitPattern._builtinWordValue)
  }

  /// Converts a typed `UnsafePointer` to an opaque C pointer.
  @_transparent
  public init<T>(_ from: UnsafePointer<T>) {
    self._rawValue = from._rawValue
  }

  /// Converts a typed `UnsafePointer` to an opaque C pointer.
  ///
  /// The result is `nil` if `from` is `nil`.
  // @_transparent
  // public init?<T>(_ from: UnsafePointer<T>?) {
  //   guard let unwrapped = from else { return nil }
  //   self.init(unwrapped)
  // }

  /// Converts a typed `UnsafeMutablePointer` to an opaque C pointer.
  @_transparent
  public init<T>(_ from: UnsafeMutablePointer<T>) {
    self._rawValue = from._rawValue
  }

  /// Converts a typed `UnsafeMutablePointer` to an opaque C pointer.
  ///
  /// The result is `nil` if `from` is `nil`.
  // @_transparent
  // public init?<T>(_ from: UnsafeMutablePointer<T>?) {
  //   guard let unwrapped = from else { return nil }
  //   self.init(unwrapped)
  // }
}

extension OpaquePointer: Equatable {
  @inlinable // unsafe-performance
  public static func == (lhs: OpaquePointer, rhs: OpaquePointer) -> Bool {
    return Bool(Builtin.cmp_eq_RawPointer(lhs._rawValue, rhs._rawValue))
  }
}

public protocol _Pointer: Equatable {
// Hashable, Strideable, CustomDebugStringConvertible, CustomReflectable {
  /// A type that represents the distance between two pointers.
  typealias Distance = Int
  
  associatedtype Pointee

  var _rawValue: Builtin.RawPointer { get }

  init(_ _rawValue: Builtin.RawPointer)
}

extension _Pointer {
  /// Creates a new typed pointer from the given opaque pointer.
  ///
  /// - Parameter from: The opaque pointer to convert to a typed pointer.
  @_transparent
  public init(_ from : OpaquePointer) {
    self.init(from._rawValue)
  }

  /// Creates a new typed pointer from the given opaque pointer.
  ///
  /// - Parameter from: The opaque pointer to convert to a typed pointer. If
  ///   `from` is `nil`, the result of this initializer is `nil`.
  // @_transparent
  // public init?(_ from : OpaquePointer?) {
  //   guard let unwrapped = from else { return nil }
  //   self.init(unwrapped)
  // }

  // /// Creates a new pointer from the given address, specified as a bit
  // /// pattern.
  // ///
  // /// The address passed as `bitPattern` must have the correct alignment for
  // /// the pointer's `Pointee` type. That is,
  // /// `bitPattern % MemoryLayout<Pointee>.alignment` must be `0`.
  // ///
  // /// - Parameter bitPattern: A bit pattern to use for the address of the new
  // ///   pointer. If `bitPattern` is zero, the result is `nil`.
  // @_transparent
  // public init?(bitPattern: Int) {
  //   if bitPattern == 0 { return nil }
  //   self.init(Builtin.inttoptr_Word(bitPattern._builtinWordValue))
  // }

  /// Creates a new pointer from the given address, specified as a bit
  /// pattern.
  ///
  /// The address passed as `bitPattern` must have the correct alignment for
  /// the pointer's `Pointee` type. That is,
  /// `bitPattern % MemoryLayout<Pointee>.alignment` must be `0`.
  ///
  /// - Parameter bitPattern: A bit pattern to use for the address of the new
  ///   pointer. If `bitPattern` is zero, the result is `nil`.
  // @_transparent
  // public init?(bitPattern: UInt) {
  //   if bitPattern == 0 { return nil }
  //   self.init(Builtin.inttoptr_Word(bitPattern._builtinWordValue))
  // }

  /// Creates a new pointer from the given pointer.
  ///
  /// - Parameter other: The typed pointer to convert.
  @_transparent
  public init(_ other: Self) {
    self.init(other._rawValue)
  }

  /// Creates a new pointer from the given pointer.
  ///
  /// - Parameter other: The typed pointer to convert. If `other` is `nil`, the
  ///   result is `nil`.
  // @_transparent
  // public init?(_ other: Self?) {
  //   guard let unwrapped = other else { return nil }
  //   self.init(unwrapped._rawValue)
  // }

  // all pointers are creatable from mutable pointers
  
  /// Creates a new pointer from the given mutable pointer.
  ///
  /// Use this initializer to explicitly convert `other` to an `UnsafeRawPointer`
  /// instance. This initializer creates a new pointer to the same address as
  /// `other` and performs no allocation or copying.
  ///
  /// - Parameter other: The typed pointer to convert.
  // @_transparent
  // public init<T>(_ other: UnsafeMutablePointer<T>) {
  //   self.init(other._rawValue)
  // }

  // /// Creates a new raw pointer from the given typed pointer.
  // ///
  // /// Use this initializer to explicitly convert `other` to an `UnsafeRawPointer`
  // /// instance. This initializer creates a new pointer to the same address as
  // /// `other` and performs no allocation or copying.
  // ///
  // /// - Parameter other: The typed pointer to convert. If `other` is `nil`, the
  // ///   result is `nil`.
  // @_transparent
  // public init?<T>(_ other: UnsafeMutablePointer<T>?) {
  //   guard let unwrapped = other else { return nil }
  //   self.init(unwrapped)
  // }
}

public protocol Comparable : Equatable {
  static func < (lhs: Self, rhs: Self) -> Bool
  static func <= (lhs: Self, rhs: Self) -> Bool
  static func >= (lhs: Self, rhs: Self) -> Bool
  static func > (lhs: Self, rhs: Self) -> Bool
}

extension Comparable {
  @inlinable
  public static func > (lhs: Self, rhs: Self) -> Bool {
    return rhs < lhs
  }

  @inlinable
  public static func <= (lhs: Self, rhs: Self) -> Bool {
    return !(rhs < lhs)
  }

  @inlinable
  public static func >= (lhs: Self, rhs: Self) -> Bool {
    return !(lhs < rhs)
  }
}

// well, this is pretty annoying
extension _Pointer /*: Equatable */ {
  @_transparent
  public static func == (lhs: Self, rhs: Self) -> Bool {
    return Bool(Builtin.cmp_eq_RawPointer(lhs._rawValue, rhs._rawValue))
  }
}

extension _Pointer /*: Comparable */ {
  @_transparent
  public static func < (lhs: Self, rhs: Self) -> Bool {
    return Bool(Builtin.cmp_ult_RawPointer(lhs._rawValue, rhs._rawValue))
  }
}

@_fixed_layout // FIXME(sil-serialize-all)
public struct ObjectIdentifier {
  @usableFromInline // FIXME(sil-serialize-all)
  internal let _value: Builtin.RawPointer

  @inlinable // FIXME(sil-serialize-all)
  public init(_ x: AnyObject) {
    self._value = Builtin.bridgeToRawPointer(x)
  }

  @inlinable // FIXME(sil-serialize-all)
  public init(_ x: Any.Type) {
    self._value = unsafeBitCast(x, to: Builtin.RawPointer.self)
  }
}

extension ObjectIdentifier: Equatable {
  @inlinable // FIXME(sil-serialize-all)
  public static func == (x: ObjectIdentifier, y: ObjectIdentifier) -> Bool {
    return Bool(Builtin.cmp_eq_RawPointer(x._value, y._value))
  }
}

extension ObjectIdentifier: Comparable {
  @inlinable // FIXME(sil-serialize-all)
  public static func < (lhs: ObjectIdentifier, rhs: ObjectIdentifier) -> Bool {
    return UInt(bitPattern: lhs) < UInt(bitPattern: rhs)
  }
}

// extension ObjectIdentifier: Hashable {
//   @inlinable
//   public func hash(into hasher: inout Hasher) {
//     hasher.combine(Int(Builtin.ptrtoint_Word(_value)))
//   }
// }

extension UInt {
  @inlinable // FIXME(sil-serialize-all)
  public init(bitPattern objectID: ObjectIdentifier) {
    self.init(Builtin.ptrtoint_Word(objectID._value))
  }
}

extension Int {
  @inlinable // FIXME(sil-serialize-all)
  public init(bitPattern objectID: ObjectIdentifier) {
    self.init(bitPattern: UInt(bitPattern: objectID))
  }
}

public protocol Equatable {
  static func == (lhs: Self, rhs: Self) -> Bool
}

extension Equatable {
  @_transparent
  public static func != (lhs: Self, rhs: Self) -> Bool {
    return !(lhs == rhs)
  }
}

@inlinable // trivial-implementation
public func === (lhs: AnyObject?, rhs: AnyObject?) -> Bool {
  switch (lhs, rhs) {
  case let (l?, r?):
    return ObjectIdentifier(l) == ObjectIdentifier(r)
  case (nil, nil):
    return true
  default:
    return false
  }
}

@inlinable // trivial-implementation
public func !== (lhs: AnyObject?, rhs: AnyObject?) -> Bool {
  return !(lhs === rhs)
}

// @_frozen // namespace
public enum MemoryLayout<T> {
  @_transparent
  public static var size: Int {
    return Int(Builtin.sizeof(T.self))
  }

  @_transparent
  public static var stride: Int {
    return Int(Builtin.strideof(T.self))
  }

  @_transparent
  public static var alignment: Int {
    return Int(Builtin.alignof(T.self))
  }
}

extension MemoryLayout {
  @_transparent
  public static func size(ofValue value: T) -> Int {
    return MemoryLayout.size
  }

  @_transparent
  public static func stride(ofValue value: T) -> Int {
    return MemoryLayout.stride
  }

  @_transparent
  public static func alignment(ofValue value: T) -> Int {
    return MemoryLayout.alignment
  }

  // @_transparent
  // public static func offset(of key: PartialKeyPath<T>) -> Int? {
  //   return key._storedInlineOffset
  // }
}

@_fixed_layout // unsafe-performance
public struct UnsafeMutablePointer<Pointee>: _Pointer {
  public typealias Distance = Int
  public let _rawValue: Builtin.RawPointer

  @_transparent
  public init(_ _rawValue : Builtin.RawPointer) {
    self._rawValue = _rawValue
  }

  @_transparent
  public init(mutating other: UnsafePointer<Pointee>) {
    self._rawValue = other._rawValue
  }

  @_transparent
  public init?(mutating other: UnsafePointer<Pointee>?) {
    guard let unwrapped = other else { return nil }
    self.init(mutating: unwrapped)
  }

/** REQUIRES BINARY INTEGER ARITHMETIC */
  // @inlinable
  // public static func allocate(capacity count: Int)
  //   -> UnsafeMutablePointer<Pointee> {
  //   let size = MemoryLayout<Pointee>.stride * count
  //   let rawPtr =
  //     Builtin.allocRaw(size._builtinWordValue, Builtin.alignof(Pointee.self))
  //   Builtin.bindMemory(rawPtr, count._builtinWordValue, Pointee.self)
  //   return UnsafeMutablePointer(rawPtr)
  // }

  @inlinable
  public func deallocate() {
    Builtin.deallocRaw(_rawValue, (-1)._builtinWordValue, (-1)._builtinWordValue)
  }
}

@_fixed_layout // unsafe-performance
public struct UnsafePointer<Pointee>: _Pointer {
  public typealias Distance = Int
  public let _rawValue: Builtin.RawPointer

  @_transparent
  public init(_ _rawValue : Builtin.RawPointer) {
    self._rawValue = _rawValue
  }

  @inlinable
  public func deallocate() {
    Builtin.deallocRaw(_rawValue, (-1)._builtinWordValue, (-1)._builtinWordValue)
  }

  @inlinable // unsafe-performance
  public var pointee: Pointee {
    @_transparent unsafeAddress {
      return self
    }
  }

  // @inlinable
  // public func withMemoryRebound<T, Result>(to type: T.Type, capacity count: Int,
  //   _ body: (UnsafePointer<T>) throws -> Result
  // ) rethrows -> Result {
  //   Builtin.bindMemory(_rawValue, count._builtinWordValue, T.self)
  //   defer {
  //     Builtin.bindMemory(_rawValue, count._builtinWordValue, Pointee.self)
  //   }
  //   return try body(UnsafePointer<T>(_rawValue))
  // }

/** REQUIRES BINARY INTEGER ARITHMETIC */

  // @inlinable
  // public subscript(i: Int) -> Pointee {
  //   @_transparent
  //   unsafeAddress {
  //     return self + i
  //   }
  // }

  // @inlinable // unsafe-performance
  // internal static var _max : UnsafePointer {
  //   return UnsafePointer(
  //     bitPattern: 0 as Int &- MemoryLayout<Pointee>.stride
  //   )._unsafelyUnwrappedUnchecked
  // }
}

/// Derive a pointer argument from a convertible pointer type.
@_transparent
public // COMPILER_INTRINSIC
func _convertPointerToPointerArgument<
  FromPointer : _Pointer,
  ToPointer : _Pointer
>(_ from: FromPointer) -> ToPointer {
  return ToPointer(from._rawValue)
}

/// Derive a pointer argument from the address of an inout parameter.
@_transparent
public // COMPILER_INTRINSIC
func _convertInOutToPointerArgument<
  ToPointer : _Pointer
>(_ from: Builtin.RawPointer) -> ToPointer {
  return ToPointer(from)
}