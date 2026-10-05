import Erdos883AdaptiveSpan22751Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength22751_7 : adaptiveNumericSpans22751_7.length = 442 := by decide +kernel
theorem adaptiveSpanEvenCache22751_7 : adaptiveSpanEven22751_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain22751_7 : adaptiveSpanEven22751_7.domainCheck 11376 = true := by decide +kernel
theorem adaptiveSpanEvenEntries22751_7 : adaptiveSpanEven22751_7.spans = coreEvenSpans 11376 0 adaptiveNumericSpans22751_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache22751_7 : adaptiveSpanWhole22751_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain22751_7 : adaptiveSpanWhole22751_7.domainCheck 11376 = true := by decide +kernel
theorem adaptiveSpanWholeEntries22751_7 : adaptiveSpanWhole22751_7.spans = coreWholeSpans 0 adaptiveNumericSpans22751_7 := by
  decide +kernel
end Erdos883Verified
