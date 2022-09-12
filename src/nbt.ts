/*
	NBT.js - a JavaScript parser for NBT archives
	by Sijmen Mulder

	I, the copyright holder of this work, hereby release it into the public
	domain. This applies worldwide.

	In case this is not legally possible: I grant anyone the right to use this
	work for any purpose, without any conditions, unless such conditions are
	required by law.
*/
import { gunzip } from "zlib";

(function () {
  "use strict";

  if (typeof ArrayBuffer === "undefined") {
    throw new Error("Missing required type ArrayBuffer");
  }
  if (typeof DataView === "undefined") {
    throw new Error("Missing required type DataView");
  }
  if (typeof Uint8Array === "undefined") {
    throw new Error("Missing required type Uint8Array");
  }

  /** @exports nbt */

  // @ts-expect-error
  let nbt = this;

  /**
   * A mapping from type names to NBT type numbers.
   * {@link module:nbt.Writer} and {@link module:nbt.Reader}
   * have correspoding methods (e.g. {@link module:nbt.Writer#int})
   * for every type.
   *
   * @type Object<string, number>
   * @see module:nbt.tagTypeNames */
  nbt.tagTypes = {
    end: 0,
    byte: 1,
    short: 2,
    int: 3,
    long: 4,
    float: 5,
    double: 6,
    byteArray: 7,
    string: 8,
    list: 9,
    compound: 10,
    intArray: 11,
    longArray: 12,
  };

  /**
   * A mapping from NBT type numbers to type names.
   *
   * @type Object<number, string>
   * @see module:nbt.tagTypes */
  nbt.tagTypeNames = {};
  (function () {
    for (let typeName in nbt.tagTypes) {
      if (nbt.tagTypes.hasOwnProperty(typeName)) {
        nbt.tagTypeNames[nbt.tagTypes[typeName]] = typeName;
      }
    }
  })();

  function hasGzipHeader(data: ArrayBuffer | Buffer) {
    let head = new Uint8Array(data.slice(0, 2));
    return head.length === 2 && head[0] === 0x1f && head[1] === 0x8b;
  }

  function encodeUTF8(str: string) {
    let array = [],
      i,
      c;
    for (i = 0; i < str.length; i++) {
      c = str.charCodeAt(i);
      if (c < 0x80) {
        array.push(c);
      } else if (c < 0x800) {
        array.push(0xc0 | (c >> 6));
        array.push(0x80 | (c & 0x3f));
      } else if (c < 0x10000) {
        array.push(0xe0 | (c >> 12));
        array.push(0x80 | ((c >> 6) & 0x3f));
        array.push(0x80 | (c & 0x3f));
      } else {
        array.push(0xf0 | ((c >> 18) & 0x07));
        array.push(0x80 | ((c >> 12) & 0x3f));
        array.push(0x80 | ((c >> 6) & 0x3f));
        array.push(0x80 | (c & 0x3f));
      }
    }
    return array;
  }

  function decodeUTF8(array: Uint8Array) {
    let codepoints = [],
      i;
    for (i = 0; i < array.length; i++) {
      if ((array[i] & 0x80) === 0) {
        codepoints.push(array[i] & 0x7f);
      } else if (
        i + 1 < array.length &&
        (array[i] & 0xe0) === 0xc0 &&
        (array[i + 1] & 0xc0) === 0x80
      ) {
        codepoints.push(((array[i] & 0x1f) << 6) | (array[i + 1] & 0x3f));
      } else if (
        i + 2 < array.length &&
        (array[i] & 0xf0) === 0xe0 &&
        (array[i + 1] & 0xc0) === 0x80 &&
        (array[i + 2] & 0xc0) === 0x80
      ) {
        codepoints.push(
          ((array[i] & 0x0f) << 12) |
            ((array[i + 1] & 0x3f) << 6) |
            (array[i + 2] & 0x3f)
        );
      } else if (
        i + 3 < array.length &&
        (array[i] & 0xf8) === 0xf0 &&
        (array[i + 1] & 0xc0) === 0x80 &&
        (array[i + 2] & 0xc0) === 0x80 &&
        (array[i + 3] & 0xc0) === 0x80
      ) {
        codepoints.push(
          ((array[i] & 0x07) << 18) |
            ((array[i + 1] & 0x3f) << 12) |
            ((array[i + 2] & 0x3f) << 6) |
            (array[i + 3] & 0x3f)
        );
      }
    }
    return String.fromCharCode.apply(null, codepoints);
  }

  /* Not all environments, in particular PhantomJS, supply
	   Uint8Array.slice() */
  function sliceUint8Array(array: Uint8Array, begin: number, end: number) {
    if ("slice" in array) {
      return array.slice(begin, end);
    } else {
      return new Uint8Array([].slice.call(array, begin, end));
    }
  }

  /**
   * In addition to the named writing methods documented below,
   * the same methods are indexed by the NBT type number as well,
   * as shown in the example below.
   *
   * @constructor
   * @see module:nbt.Reader
   *
   * @example
   * let writer = new nbt.Writer();
   *
   * // all equivalent
   * writer.int(42);
   * writer[3](42);
   * writer(nbt.tagTypes.int)(42);
   *
   * // overwrite the second int
   * writer.offset = 0;
   * writer.int(999);
   *
   * return writer.buffer; */
  nbt.Writer = function () {
    let self = this;

    /* Will be resized (x2) on write if necessary. */
    let buffer = new ArrayBuffer(1024);

    /* These are recreated when the buffer is */
    let dataView = new DataView(buffer);
    let arrayView = new Uint8Array(buffer);

    /**
     * The location in the buffer where bytes are written or read.
     * This increases after every write, but can be freely changed.
     * The buffer will be resized when necessary.
     *
     * @type number */
    this.offset = 0;

    // Ensures that the buffer is large enough to write `size` bytes
    // at the current `self.offset`.
    function accommodate(size: number) {
      let requiredLength = self.offset + size;
      if (buffer.byteLength >= requiredLength) {
        return;
      }

      let newLength = buffer.byteLength;
      while (newLength < requiredLength) {
        newLength *= 2;
      }

      let newBuffer = new ArrayBuffer(newLength);
      let newArrayView = new Uint8Array(newBuffer);
      newArrayView.set(arrayView);

      // If there's a gap between the end of the old buffer
      // and the start of the new one, we need to zero it out
      if (self.offset > buffer.byteLength) {
        newArrayView.fill(0, buffer.byteLength, self.offset);
      }

      buffer = newBuffer;
      dataView = new DataView(newBuffer);
      arrayView = newArrayView;
    }

    function write(dataType: string, size: number, value: any) {
      accommodate(size);
      // @ts-expect-error
      dataView["set" + dataType](self.offset, value);
      self.offset += size;
      return self;
    }

    /**
     * Returns the writen data as a slice from the internal buffer,
     * cutting off any padding at the end.
     *
     * @returns {ArrayBuffer} a [0, offset] slice of the interal buffer */
    this.getData = function () {
      accommodate(0); /* make sure the offset is inside the buffer */
      return buffer.slice(0, self.offset);
    };

    /**
     * @method module:nbt.Writer#byte
     * @param {number} value - a signed byte
     * @returns {module:nbt.Writer} itself */
    this[nbt.tagTypes.byte] = write.bind(this, "Int8", 1);

    /**
     * @method module:nbt.Writer#ubyte
     * @param {number} value - an unsigned byte
     * @returns {module:nbt.Writer} itself */
    this.ubyte = write.bind(this, "Uint8", 1);

    /**
     * @method module:nbt.Writer#short
     * @param {number} value - a signed 16-bit integer
     * @returns {module:nbt.Writer} itself */
    this[nbt.tagTypes.short] = write.bind(this, "Int16", 2);

    /**
     * @method module:nbt.Writer#int
     * @param {number} value - a signed 32-bit integer
     * @returns {module:nbt.Writer} itself */
    this[nbt.tagTypes.int] = write.bind(this, "Int32", 4);

    /**
     * @method module:nbt.Writer#float
     * @param {number} value - a signed 32-bit float
     * @returns {module:nbt.Writer} itself */
    this[nbt.tagTypes.float] = write.bind(this, "Float32", 4);

    /**
     * @method module:nbt.Writer#float
     * @param {number} value - a signed 64-bit float
     * @returns {module:nbt.Writer} itself */
    this[nbt.tagTypes.double] = write.bind(this, "Float64", 8);

    /**
     * As JavaScript does not support 64-bit integers natively, this
     * method takes an array of two 32-bit integers that make up the
     * upper and lower halves of the long.
     *
     * @method module:nbt.Writer#long
     * @param {Array.<number>} value - [upper, lower]
     * @returns {module:nbt.Writer} itself */
    this[nbt.tagTypes.long] = function (value: number[]) {
      self.int(value[0]);
      self.int(value[1]);
      return self;
    };

    /**
     * @method module:nbt.Writer#byteArray
     * @param {Array.<number>|Uint8Array|Buffer} value
     * @returns {module:nbt.Writer} itself */
    this[nbt.tagTypes.byteArray] = function (
      value: number[] | Uint8Array | Buffer
    ) {
      this.int(value.length);
      accommodate(value.length);
      arrayView.set(value, this.offset);
      this.offset += value.length;
      return this;
    };

    /**
     * @method module:nbt.Writer#intArray
     * @param {Array.<number>} value
     * @returns {module:nbt.Writer} itself */
    this[nbt.tagTypes.intArray] = function (value: number[]) {
      this.int(value.length);
      let i;
      for (i = 0; i < value.length; i++) {
        this.int(value[i]);
      }
      return this;
    };

    /**
     * @method module:nbt.Writer#longArray
     * @param {Array.<number>} value
     * @returns {module:nbt.Writer} itself */
    this[nbt.tagTypes.longArray] = function (value: number[]) {
      this.int(value.length);
      let i;
      for (i = 0; i < value.length; i++) {
        this.long(value[i]);
      }
      return this;
    };

    /**
     * @method module:nbt.Writer#string
     * @param {string} value
     * @returns {module:nbt.Writer} itself */
    this[nbt.tagTypes.string] = function (value: string) {
      let bytes = encodeUTF8(value);
      this.short(bytes.length);
      accommodate(bytes.length);
      arrayView.set(bytes, this.offset);
      this.offset += bytes.length;
      return this;
    };

    /**
     * @method module:nbt.Writer#list
     * @param {Object} value
     * @param {number} value.type - the NBT type number
     * @param {Array} value.value - an array of values
     * @returns {module:nbt.Writer} itself */
    this[nbt.tagTypes.list] = function (value: { type: number; value: any[] }) {
      this.byte(nbt.tagTypes[value.type]);
      this.int(value.value.length);
      let i;
      for (i = 0; i < value.value.length; i++) {
        this[value.type](value.value[i]);
      }
      return this;
    };

    /**
     * @method module:nbt.Writer#compound
     * @param {Object} value - a key/value map
     * @param {Object} value.KEY
     * @param {string} value.KEY.type - the NBT type number
     * @param {Object} value.KEY.value - a value matching the type
     * @returns {module:nbt.Writer} itself
     *
     * @example
     * writer.compound({
     *     foo: { type: 'int', value: 12 },
     *     bar: { type: 'string', value: 'Hello, World!' }
     * }); */
    this[nbt.tagTypes.compound] = function (value: {
      KEY: { type: string; value: Record<string, any> };
      [x: string]: any;
    }) {
      let self = this;
      Object.keys(value).map(function (key) {
        self.byte(nbt.tagTypes[value[key].type]);
        self.string(key);
        self[value[key].type](value[key].value);
      });
      this.byte(nbt.tagTypes.end);
      return this;
    };

    let typeName;
    for (typeName in nbt.tagTypes) {
      if (nbt.tagTypes.hasOwnProperty(typeName)) {
        this[typeName] = this[nbt.tagTypes[typeName]];
      }
    }
  };

  /**
   * In addition to the named writing methods documented below,
   * the same methods are indexed by the NBT type number as well,
   * as shown in the example below.
   *
   * @constructor
   * @see module:nbt.Writer
   *
   * @example
   * let reader = new nbt.Reader(buf);
   * int x = reader.int();
   * int y = reader[3]();
   * int z = reader[nbt.tagTypes.int](); */
  nbt.Reader = function (buffer: Uint8Array | Buffer) {
    if (!buffer) {
      throw new Error('Argument "buffer" is falsy');
    }

    let self = this;

    /**
     * The current location in the buffer. Can be freely changed
     * within the bounds of the buffer.
     *
     * @type number */
    this.offset = 0;

    let arrayView = new Uint8Array(buffer);
    let dataView = new DataView(arrayView.buffer);

    function read(dataType: string, size: number) {
      // @ts-expect-error
      let val = dataView["get" + dataType](self.offset);
      self.offset += size;
      return val;
    }

    /**
     * @method module:nbt.Reader#byte
     * @returns {number} the read byte */
    this[nbt.tagTypes.byte] = read.bind(this, "Int8", 1);

    /**
     * @method module:nbt.Reader#byte
     * @returns {number} the read unsigned byte */
    this.ubyte = read.bind(this, "Uint8", 1);

    /**
     * @method module:nbt.Reader#short
     * @returns {number} the read signed 16-bit short  */
    this[nbt.tagTypes.short] = read.bind(this, "Int16", 2);

    /**
     * @method module:nbt.Reader#int
     * @returns {number} the read signed 32-bit integer */
    this[nbt.tagTypes.int] = read.bind(this, "Int32", 4);

    /**
     * @method module:nbt.Reader#float
     * @returns {number} the read signed 32-bit float */
    this[nbt.tagTypes.float] = read.bind(this, "Float32", 4);

    /**
     * @method module:nbt.Reader#double
     * @returns {number} the read signed 64-bit float */
    this[nbt.tagTypes.double] = read.bind(this, "Float64", 8);

    /**
     * As JavaScript does not not natively support 64-bit
     * integers, the value is returned as an array of two
     * 32-bit integers, the upper and the lower.
     *
     * @method module:nbt.Reader#long
     * @returns {Array.<number>} [upper, lower] */
    this[nbt.tagTypes.long] = function () {
      return [this.int(), this.int()];
    };

    /**
     * @method module:nbt.Reader#byteArray
     * @returns {Array.<number>} the read array */
    this[nbt.tagTypes.byteArray] = function () {
      let length = this.int();
      let bytes = [];
      let i;
      for (i = 0; i < length; i++) {
        bytes.push(this.byte());
      }
      return bytes;
    };

    /**
     * @method module:nbt.Reader#intArray
     * @returns {Array.<number>} the read array of 32-bit ints */
    this[nbt.tagTypes.intArray] = function () {
      let length = this.int();
      let ints = [];
      let i;
      for (i = 0; i < length; i++) {
        ints.push(this.int());
      }
      return ints;
    };

    /**
     * As JavaScript does not not natively support 64-bit
     * integers, the value is returned as an array of arrays of two
     * 32-bit integers, the upper and the lower.
     *
     * @method module:nbt.Reader#longArray
     * @returns {Array.<number>} the read array of 64-bit ints
     *     split into [upper, lower] */
    this[nbt.tagTypes.longArray] = function () {
      let length = this.int();
      let longs = [];
      let i;
      for (i = 0; i < length; i++) {
        longs.push(this.long());
      }
      return longs;
    };

    /**
     * @method module:nbt.Reader#string
     * @returns {string} the read string */
    this[nbt.tagTypes.string] = function () {
      let length = this.short();
      let slice = sliceUint8Array(arrayView, this.offset, this.offset + length);
      this.offset += length;
      return decodeUTF8(slice);
    };

    /**
     * @method module:nbt.Reader#list
     * @returns {{type: string, value: Array}}
     *
     * @example
     * reader.list();
     * // -> { type: 'string', values: ['foo', 'bar'] } */
    this[nbt.tagTypes.list] = function () {
      let type = this.byte();
      let length = this.int();
      let values = [];
      let i;
      for (i = 0; i < length; i++) {
        values.push(this[type]());
      }
      return { type: nbt.tagTypeNames[type], value: values };
    };

    /**
     * @method module:nbt.Reader#compound
     * @returns {Object.<string, { type: string, value }>}
     *
     * @example
     * reader.compound();
     * // -> { foo: { type: int, value: 42 },
     * //      bar: { type: string, value: 'Hello! }} */
    this[nbt.tagTypes.compound] = function () {
      let values: {
        [x: string]: {
          type: string;
          value: any[];
        };
      } = {};
      while (true) {
        let type = this.byte();
        if (type === nbt.tagTypes.end) {
          break;
        }
        let name = this.string();
        let value = this[type]();
        values[name] = { type: nbt.tagTypeNames[type], value: value };
      }
      return values;
    };

    let typeName;
    for (typeName in nbt.tagTypes) {
      if (nbt.tagTypes.hasOwnProperty(typeName)) {
        this[typeName] = this[nbt.tagTypes[typeName]];
      }
    }
  };

  /**
   * @param {Object} value - a named compound
   * @param {string} value.name - the top-level name
   * @param {Object} value.value - a compound
   * @returns {ArrayBuffer}
   *
   * @see module:nbt.parseUncompressed
   * @see module:nbt.Writer#compound
   *
   * @example
   * nbt.writeUncompressed({
   *     name: 'My Level',
   *     value: {
   *         foo: { type: int, value: 42 },
   *         bar: { type: string, value: 'Hi!' }
   *     }
   * }); */
  nbt.writeUncompressed = function (value: {
    name: string;
    value: Record<string, any>;
  }) {
    if (!value) {
      throw new Error('Argument "value" is falsy');
    }

    let writer = new nbt.Writer();

    writer.byte(nbt.tagTypes.compound);
    writer.string(value.name);
    writer.compound(value.value);

    return writer.getData();
  };

  /**
   * @param {ArrayBuffer|Buffer} data - an uncompressed NBT archive
   * @returns {{name: string, value: Object.<string, Object>}}
   *     a named compound
   *
   * @see module:nbt.parse
   * @see module:nbt.writeUncompressed
   *
   * @example
   * nbt.readUncompressed(buf);
   * // -> { name: 'My Level',
   * //      value: { foo: { type: int, value: 42 },
   * //               bar: { type: string, value: 'Hi!' }}} */
  nbt.parseUncompressed = function (data: ArrayBuffer | Buffer) {
    if (!data) {
      throw new Error('Argument "data" is falsy');
    }

    let reader = new nbt.Reader(data);

    let type = reader.byte();
    if (type !== nbt.tagTypes.compound) {
      throw new Error("Top tag should be a compound");
    }

    return {
      name: reader.string(),
      value: reader.compound(),
    };
  };

  /**
   * @callback parseCallback
   * @param {Object} error
   * @param {Object} result - a named compound
   * @param {string} result.name - the top-level name
   * @param {Object} result.value - the top-level compound */

  /**
   * This accepts both gzipped and uncompressd NBT archives.
   * If the archive is uncompressed, the callback will be
   * called directly from this method. For gzipped files, the
   * callback is async.
   *
   * For use in the browser, window.zlib must be defined to decode
   * compressed archives. It will be passed a Buffer if the type is
   * available, or an Uint8Array otherwise.
   *
   * @param {ArrayBuffer|Buffer} data - gzipped or uncompressed data
   * @param {parseCallback} callback
   *
   * @see module:nbt.parseUncompressed
   * @see module:nbt.Reader#compound
   *
   * @example
   * nbt.parse(buf, function(error, results) {
   *     if (error) {
   *         throw error;
   *     }
   *     console.log(result.name);
   *     console.log(result.value.foo);
   * }); */
  nbt.parse = function (
    data: ArrayBuffer,
    callback: (
      error: null | Error,
      results: Record<string, any> | Record<string, any>[] | null
    ) => void
  ) {
    if (!data) {
      throw new Error('Argument "data" is falsy');
    }

    let self = this;

    if (!hasGzipHeader(data)) {
      callback(null, self.parseUncompressed(data));
    } else {
      /* zlib.gunzip take a Buffer, at least in Node, so try to convert
			   if possible. */
      let buffer;
      if (data.byteLength) {
        buffer = data;
      } else if (typeof Buffer !== "undefined") {
        buffer = new Buffer(data);
      } else {
        /* In the browser? Unknown zlib library. Let's settle for
				   Uint8Array and see what happens. */
        buffer = new Uint8Array(data);
      }

      gunzip(buffer, function (error, uncompressed) {
        if (error) {
          callback(error, null);
        } else {
          callback(null, self.parseUncompressed(uncompressed));
        }
      });
    }
  };
  // @ts-expect-error
}.apply(typeof exports !== "undefined" ? exports : (window.nbt = {})));
