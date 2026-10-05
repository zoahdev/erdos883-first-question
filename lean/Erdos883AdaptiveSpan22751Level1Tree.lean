import Erdos883AdaptiveSpan22751Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength22751_1 : adaptiveNumericSpans22751_1.length = 442 := by decide +kernel
theorem adaptiveSpanEvenCache22751_1 : adaptiveSpanEven22751_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain22751_1 : adaptiveSpanEven22751_1.domainCheck 11376 = true := by decide +kernel
theorem adaptiveSpanEvenEntries22751_1 : adaptiveSpanEven22751_1.spans = coreEvenSpans 11376 0 adaptiveNumericSpans22751_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache22751_1 : adaptiveSpanWhole22751_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain22751_1 : adaptiveSpanWhole22751_1.domainCheck 11376 = true := by decide +kernel
theorem adaptiveSpanWholeEntries22751_1 : adaptiveSpanWhole22751_1.spans = coreWholeSpans 0 adaptiveNumericSpans22751_1 := by
  decide +kernel
end Erdos883Verified
