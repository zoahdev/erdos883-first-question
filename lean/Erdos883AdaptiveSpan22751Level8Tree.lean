import Erdos883AdaptiveSpan22751Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength22751_8 : adaptiveNumericSpans22751_8.length = 442 := by decide +kernel
theorem adaptiveSpanEvenCache22751_8 : adaptiveSpanEven22751_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain22751_8 : adaptiveSpanEven22751_8.domainCheck 11376 = true := by decide +kernel
theorem adaptiveSpanEvenEntries22751_8 : adaptiveSpanEven22751_8.spans = coreEvenSpans 11376 0 adaptiveNumericSpans22751_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache22751_8 : adaptiveSpanWhole22751_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain22751_8 : adaptiveSpanWhole22751_8.domainCheck 11376 = true := by decide +kernel
theorem adaptiveSpanWholeEntries22751_8 : adaptiveSpanWhole22751_8.spans = coreWholeSpans 0 adaptiveNumericSpans22751_8 := by
  decide +kernel
end Erdos883Verified
