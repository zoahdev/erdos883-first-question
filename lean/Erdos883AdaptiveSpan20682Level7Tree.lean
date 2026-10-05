import Erdos883AdaptiveSpan20682Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength20682_7 : adaptiveNumericSpans20682_7.length = 430 := by decide +kernel
theorem adaptiveSpanEvenCache20682_7 : adaptiveSpanEven20682_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain20682_7 : adaptiveSpanEven20682_7.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanEvenEntries20682_7 : adaptiveSpanEven20682_7.spans = coreEvenSpans 10341 0 adaptiveNumericSpans20682_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache20682_7 : adaptiveSpanWhole20682_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain20682_7 : adaptiveSpanWhole20682_7.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanWholeEntries20682_7 : adaptiveSpanWhole20682_7.spans = coreWholeSpans 0 adaptiveNumericSpans20682_7 := by
  decide +kernel
end Erdos883Verified
