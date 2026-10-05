import Erdos883AdaptiveSpan22751Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength22751_4 : adaptiveNumericSpans22751_4.length = 442 := by decide +kernel
theorem adaptiveSpanEvenCache22751_4 : adaptiveSpanEven22751_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain22751_4 : adaptiveSpanEven22751_4.domainCheck 11376 = true := by decide +kernel
theorem adaptiveSpanEvenEntries22751_4 : adaptiveSpanEven22751_4.spans = coreEvenSpans 11376 0 adaptiveNumericSpans22751_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache22751_4 : adaptiveSpanWhole22751_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain22751_4 : adaptiveSpanWhole22751_4.domainCheck 11376 = true := by decide +kernel
theorem adaptiveSpanWholeEntries22751_4 : adaptiveSpanWhole22751_4.spans = coreWholeSpans 0 adaptiveNumericSpans22751_4 := by
  decide +kernel
end Erdos883Verified
